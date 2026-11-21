"""Exercise the handoffs without Lean, Lake, Git, or network access."""

from concurrent.futures import ThreadPoolExecutor
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import lean_worker as worker


class HandoffTests(unittest.TestCase):
    def setUp(self):
        scratch = tempfile.TemporaryDirectory()
        self.addCleanup(scratch.cleanup)
        self.root = Path(scratch.name)
        self.state = self.root / "state"
        self.state.mkdir()
        self.parent = "a" * 40
        self.path = "Lean/MOC/Claim.lean"
        self.sources = {self.path: b"base", "Lean/MOC.lean": b"umbrella"}
        self.sources.update({f"Lean/{name}": b"pin" for name in worker.PINNED})
        worker.sync_snapshot(self.root, self.sources | {self.path: b"new proof"})
        worker.sync_snapshot(self.state / "bases" / self.parent, self.sources)
        worker.atomic_json(self.state / "base.json", {
            "parent": self.parent, "digest": worker.sources_digest(self.sources),
        })

    def capture(self):
        inbox = self.state / "intents"
        inbox.mkdir()
        (inbox / "proof.txt").write_text(f"lean: exact proof\n{self.path}\n")
        with patch.object(worker, "ROOT", self.root), patch.object(worker, "git") as mocked_git:
            worker.collect_intents(self.state)
            mocked_git.assert_not_called()

    def run_build(self, _project, sources, log):
        self.assertEqual(sources[self.path], b"new proof")
        log.parent.mkdir(exist_ok=True)
        log.write_text("compiler fixture\n")
        return True, []

    def test_one_build_for_draft_and_candidate(self):
        self.capture()
        (self.root / self.path).write_bytes(b"edit after capture")
        expected = self.sources | {self.path: b"new proof"}
        with patch.object(worker, "build", side_effect=self.run_build) as compiler, \
                patch.object(worker, "git") as mocked_git, ThreadPoolExecutor(2) as pool:
            draft = pool.submit(worker.audited_snapshot, self.state, expected, self.state / "status.json")
            candidate = pool.submit(worker.audit_pending, self.state)
            self.assertEqual(draft.result()["state"], "passed")
            candidate.result()
            compiler.assert_called_once()
            mocked_git.assert_not_called()
        self.assertEqual(len(list((self.state / "verified").iterdir())), 1)

    def test_failed_candidate_reports_diagnostics_and_cannot_commit(self):
        def fail(_project, _sources, log):
            log.parent.mkdir(exist_ok=True)
            log.write_text("error: MOC/Claim.lean:12:3: fixture failure\n")
            return False, []

        self.capture()
        with patch.object(worker, "build", side_effect=fail):
            worker.audit_pending(self.state)
        self.assertFalse(list((self.state / "verified").glob("*")))
        self.assertIn("fixture failure", (self.state / "candidate.json").read_text())
        self.assertEqual(len(list((self.state / "rejected").iterdir())), 1)

    def test_commit_uses_receipt_and_original_subject_without_compiling(self):
        self.capture()
        with patch.object(worker, "build", side_effect=self.run_build):
            worker.audit_pending(self.state)
        event, = (self.state / "verified").iterdir()
        outputs = {
            ("rev-parse", "HEAD"): self.parent.encode(),
            ("rev-parse", f"{self.parent}^{{tree}}"): b"old-tree",
            ("write-tree",): b"new-tree",
        }

        def fake_git(_repo, *args, **kwargs):
            if args[0] == "hash-object":
                self.assertEqual(kwargs["data"], b"new proof")
                return b"blob"
            if args[0] == "commit-tree":
                self.assertEqual(args[-2:], ("-m", "lean: exact proof"))
                return b"new-commit"
            return outputs.get(args, b"")

        def export(_state, _repo, parent):
            self.assertEqual(parent, "new-commit")

        with patch.object(worker, "git", side_effect=fake_git), \
                patch.object(worker, "publish_base", side_effect=export), \
                patch.object(worker, "tree_sources", return_value=self.sources | {self.path: b"new proof"}), \
                patch.object(worker, "build") as compiler:
            worker.process_commit(self.state, self.root, event)
            compiler.assert_not_called()
        self.assertIn("new-commit", (self.state / "committed" / event.name / "receipt.json").read_text())

    def test_commit_rejects_mutated_bundle_before_git(self):
        self.capture()
        with patch.object(worker, "build", side_effect=self.run_build):
            worker.audit_pending(self.state)
        event, = (self.state / "verified").iterdir()
        (event / self.path).write_bytes(b"unverified substitution")
        with patch.object(worker, "git") as mocked_git:
            worker.process_commit(self.state, self.root, event)
            mocked_git.assert_not_called()
        self.assertTrue((self.state / "rejected" / event.name).exists())

    def test_push_uses_main_and_the_remote_fast_forward_base(self):
        calls = []
        published = "remote-tip"

        def fake_git(_repo, *args, **_kwargs):
            nonlocal published
            calls.append(args)
            if args[:2] == ("rev-parse", "FETCH_HEAD"):
                return b"remote-tip"
            if args[0] == "update-ref":
                published = args[2]
            if args[0] == "rev-parse":
                return published.encode()
            if args[0] == "rev-list":
                return b"audited-tip" if published == "remote-tip" else b""
            return b""

        with patch.object(worker, "publisher_repo", return_value=self.root), \
                patch.object(worker, "require_publication_remote"), \
                patch.object(worker, "git", side_effect=fake_git):
            self.assertEqual(worker.push_batches(self.state, "main", 5, once=True, flush=True), 0)
            with self.assertRaisesRegex(RuntimeError, "Publication requires main"):
                worker.push_batches(self.state, "moc-verified", 5, once=True, flush=True)
        self.assertIn(("merge-base", "--is-ancestor", "remote-tip", "HEAD"), calls)
        self.assertEqual([args for args in calls if args[0] == "push"],
                         [("push", "origin", "audited-tip:refs/heads/main")])

    def test_build_driver_limits_affinity_and_sanitizes_import_paths(self):
        shim = self.root / "taskset"
        shim.write_text(
            '#!/bin/bash\nprintf "%s\\n" "$LEAN_NUM_THREADS" "${LEAN_PATH-unset}" "$@"\n'
        )
        shim.chmod(0o755)
        env = os.environ | {"PATH": f"{self.root}:{os.environ['PATH']}", "LEAN_PATH": "unexpected"}
        command = ["bash", str(worker.BUILD_DRIVER), "audit"]
        result = subprocess.run(command + ["0,2,4,6", "Snapshot.lean"], env=env,
                                capture_output=True, text=True, check=True)
        self.assertEqual(result.stdout.splitlines(),
                         ["4", "unset", "-c", "0,2,4,6", "lake", "env", "lean", "-j4", "Snapshot.lean"])
        invalid = subprocess.run(command + ["0-7", "Snapshot.lean"], env=env, capture_output=True)
        self.assertEqual(invalid.returncode, 2)


if __name__ == "__main__":
    unittest.main()

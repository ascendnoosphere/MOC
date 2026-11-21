#!/usr/bin/env python3
"""Filesystem handoffs for the independent Lean build and publication workers."""

import argparse
from contextlib import contextmanager
import fcntl
from hashlib import sha256
import json
import os
from pathlib import Path, PurePosixPath
import re
import shutil
import stat
import subprocess
import sys
import tempfile
import time
from urllib.parse import urlsplit

ROOT = Path(__file__).resolve().parents[1]
BUILD_DRIVER = ROOT / "Code/lean-build.sh"
PUBLISH_DRIVER = ROOT / "Code/lean-publish.sh"
PUBLISH_BRANCH = "moc-verified"
PUBLISH_URL = "https://github.com/ascendnoosphere/MOC"
PINNED = ("lean-toolchain", "lakefile.toml", "lake-manifest.json")
AUDIT = """
open BigOperators Matrix

example : MOC.MOCIsTrue ↔
    ∀ (n : ℕ) (a b : Fin n → ℂ) (U : Matrix (Fin n) (Fin n) ℂ),
      (U * Uᴴ = 1 ∧ Uᴴ * U = 1) →
        (diagonal a + U * diagonal b * Uᴴ).det ∈ convexHull ℝ
          (Set.range (fun σ : Equiv.Perm (Fin n) => ∏ j, (a (σ j) + b j))) :=
  Iff.rfl

open Lean Elab Command Meta in
run_cmd do
  let env ← getEnv
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let declarations := env.constants.toList.filter fun (name, decl) =>
    if let some idx := env.getModuleIdxFor? name then
      (`MOC).isPrefixOf env.allImportedModuleNames[idx.toNat]! && !decl.isUnsafe
    else false
  if declarations.isEmpty then
    throwError "The MOC worker audit found no declarations"
  let audit := ((declarations.forM fun (name, _) => CollectAxioms.collect name).run env).run {}
  let extra := audit.2.axioms.filter (fun a => !allowed.contains a)
  unless extra.isEmpty do
    for (name, _) in declarations do
      let unapproved := (← collectAxioms name).filter fun a => !allowed.contains a
      unless unapproved.isEmpty do
        throwError "{name} depends on unapproved axioms {unapproved}"
    throwError "Unapproved axioms in MOC audit: {extra}"
  for (name, decl) in declarations do
    let type := decl.type
    if type.isConstOf ``MOC.MOCIsTrue ||
        (type.isForall && type.bindingDomain!.isConstOf ``Nat) then
      if ← liftTermElabM (isDefEq type (mkConst ``MOC.MOCIsTrue)) then
        logInfo m!"MOC_WORKER_UNRESTRICTED_VERIFIED {name} {← collectAxioms name}"
  logInfo m!"MOC_WORKER_AUDITED {declarations.length} safe declarations"
"""


def report(message):
    print(message, flush=True)


def atomic_json(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, tmp = tempfile.mkstemp(dir=path.parent)
    with os.fdopen(fd, "w") as out:
        json.dump(value, out, sort_keys=True)
        out.write("\n")
    os.replace(tmp, path)


@contextmanager
def lock(path, *, wait=True):
    with path.open("a") as out:
        flags = fcntl.LOCK_EX if wait else fcntl.LOCK_EX | fcntl.LOCK_NB
        try:
            fcntl.flock(out, flags)
        except BlockingIOError:
            raise RuntimeError(f"Another worker holds {path.name}") from None
        yield


def git(cwd, *args, data=None, check=True):
    return subprocess.run(
        ["bash", str(PUBLISH_DRIVER), "git", "-C", str(cwd), *args],
        input=data, stdout=subprocess.PIPE, check=check,
    ).stdout


def proof_path(path):
    return path == "Lean/MOC.lean" or re.fullmatch(
        r"Lean/MOC/(?:[A-Za-z][A-Za-z0-9_]*/)*[A-Za-z][A-Za-z0-9_]*\.lean", path
    ) is not None


def build_path(path):
    return proof_path(path) or path in {f"Lean/{name}" for name in PINNED}


def check_queue_path(raw):
    name = PurePosixPath(raw)
    if not name.parts or raw != str(name) or name.is_absolute() or ".." in name.parts:
        raise RuntimeError(f"Expected a repository-relative path: {raw!r}")
    if proof_path(raw) or raw in {
        "README.md", "Lean/README.md", "AGENTS.md", "Code/lean-workflow.sh", "Code/lean-build.sh",
        "Code/lean-publish.sh", "Code/lean_worker.py", "Code/lean_fix.py",
        "Code/merge-verified.sh", "Code/test_lean_workflow.py"
    } or (name.parts[0] == "Docs" and name.suffix == ".md"):
        return raw
    raise RuntimeError(f"Path is outside Lean workflow publication scope: {raw!r}")


def worktree_sources(root=None):
    if root is None:
        root = ROOT
    lean = root / "Lean"
    files = [lean / name for name in (*PINNED, "MOC.lean")]
    files.extend(p for p in (lean / "MOC").rglob("*.lean") if proof_path(p.relative_to(root).as_posix()))
    return {p.relative_to(root).as_posix(): read_plain_file(p) for p in files}


def read_plain_file(path):
    if path.resolve() != path:
        raise RuntimeError(f"Expected a regular, nonsymlink file: {path}")
    fd = os.open(path, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK)
    with os.fdopen(fd, "rb") as stream:
        if not stat.S_ISREG(os.fstat(stream.fileno()).st_mode):
            raise RuntimeError(f"Expected a regular, nonsymlink file: {path}")
        return stream.read()


def sources_digest(sources):
    contents = [(name, sha256(data).hexdigest()) for name, data in sorted(sources.items())]
    return sha256(json.dumps(contents).encode()).hexdigest()


def sync_snapshot(project, sources):
    project.mkdir(parents=True, exist_ok=True)
    lean = project / "Lean"
    removed = False
    for old_path in lean.glob("MOC/**/*.lean"):
        if old_path.relative_to(project).as_posix() not in sources:
            old_path.unlink()
            removed = True
    if removed and (lean / ".lake/build").exists():
        shutil.rmtree(lean / ".lake/build")
    for name, data in sources.items():
        path = project / name
        path.parent.mkdir(parents=True, exist_ok=True)
        if not path.is_file() or path.read_bytes() != data:
            path.write_bytes(data)


def build(project, sources, log):
    required = {"Lean/MOC.lean", "Lean/MOC/Claim.lean", *[f"Lean/{name}" for name in PINNED]}
    missing = required - sources.keys()
    if missing:
        log.parent.mkdir(parents=True, exist_ok=True)
        log.write_text(f"Required Lean sources missing: {', '.join(sorted(missing))}\n")
        return False, []
    sync_snapshot(project, sources)
    lean = project / "Lean"
    packages = lean / ".lake" / "packages"
    packages.parent.mkdir(exist_ok=True)
    if not packages.is_symlink():
        shared = ROOT / "Lean" / ".lake" / "packages"
        if not shared.is_dir():
            raise RuntimeError("Prepare Lean dependencies with lake build before starting the worker")
        packages.symlink_to(shared, target_is_directory=True)

    modules = sorted(
        path.removeprefix("Lean/").removesuffix(".lean").replace("/", ".")
        for path in sources if proof_path(path)
    )
    audit_file = "MOCWorkerAudit.lean"
    (lean / audit_file).write_text("".join(f"import {module}\n" for module in modules) + AUDIT)
    cores = sorted(os.sched_getaffinity(0))[:4]
    cpu_list = ",".join(str(cpu) for cpu in cores)
    commands = [
        ["bash", str(BUILD_DRIVER), "compile", cpu_list, *[f"+{module}" for module in modules]],
        ["bash", str(BUILD_DRIVER), "audit", cpu_list, audit_file],
    ]
    log.parent.mkdir(parents=True, exist_ok=True)
    with log.open("wb") as out:
        audit_offset = 0
        for index, command in enumerate(commands):
            out.write((f"$ {' '.join(command)}\n").encode())
            out.flush()
            audit_offset = out.tell()
            result = subprocess.run(
                command, cwd=lean, stdout=out, stderr=subprocess.STDOUT,
            )
            if result.returncode:
                return False, []
            if index == 0 and b"uses 'sorry'" in log.read_bytes():
                return False, []
    result = log.read_bytes()
    audit = result[audit_offset:].decode(errors="replace")
    prefix = r"^(?:MOCWorkerAudit\.lean:\d+:\d+: info: )?"
    proofs = re.findall(prefix + r"MOC_WORKER_UNRESTRICTED_VERIFIED (.+)$", audit, re.MULTILINE)
    audited = re.search(prefix + r"MOC_WORKER_AUDITED \d+ safe declarations$", audit, re.MULTILINE)
    return audited is not None, proofs


def audited_snapshot(state, sources, status_file):
    """One compilation per source digest and audit version, shared by both build lanes."""
    digest = sources_digest(sources)
    version = sha256(AUDIT.encode() + BUILD_DRIVER.read_bytes()).hexdigest()[:16]
    key = f"{version}-{digest}"
    cache = state / "audits" / f"{key}.json"
    with lock(state / "build.lock"):
        if cache.exists():
            result = json.loads(cache.read_text())
        else:
            log = state / "logs" / f"build-{key}.log"
            atomic_json(status_file, {"digest": digest, "state": "building", "log": str(log)})
            report(f"Building {digest[:12]}: {log}")
            success, proofs = build(state / "watch" / "project", sources, log)
            lines = log.read_text(errors="replace").splitlines()
            diagnostics = [line for line in lines if "error:" in line or "uses 'sorry'" in line]
            result = {
                "digest": digest, "state": "passed" if success else "failed", "log": str(log),
                "unrestricted": proofs, "diagnostics": (diagnostics or lines[-6:])[:12] if not success else [],
            }
            atomic_json(cache, result)
            report(f"Build {result['state']} for {digest[:12]}: {log}")
        atomic_json(status_file, result)
        return result


def watch(state, once):
    with lock(state / "watch.lock", wait=False):
        last = None
        while True:
            collect_intents(state)
            audit_pending(state)
            try:
                sources = worktree_sources()
                digest = sources_digest(sources)
                if digest != last and not once:
                    time.sleep(2)
                    if sources != worktree_sources():
                        continue
            except FileNotFoundError:
                if once:
                    raise
                time.sleep(1)
                continue
            if digest != last:
                result = audited_snapshot(state, sources, state / "status.json")
                last = digest
                if once:
                    return int(result["state"] != "passed")
            time.sleep(1)


def check_subject(subject):
    if not subject.strip() or "\n" in subject or "\r" in subject:
        raise RuntimeError("Provide a one-line commit subject")


def collect_intents(state):
    """B captures the files explicitly listed in A's completed handoff."""
    inbox = state / "intents"
    inbox.mkdir(exist_ok=True)
    pending = state / "pending"
    pending.mkdir(exist_ok=True)
    archive = state / "received"
    archive.mkdir(exist_ok=True)
    for note in sorted(inbox.glob("*.txt")):
        try:
            lines = read_plain_file(note).decode().splitlines()
            subject = lines[0] if lines else ""
            check_subject(subject)
            paths = sorted({check_queue_path(line) for line in lines[1:] if line})
            if not paths:
                raise RuntimeError("List at least one repository-relative source path")
            with tempfile.TemporaryDirectory(dir=state, prefix="intent-") as tmp:
                stage = Path(tmp)
                files = {}
                for name in paths:
                    path = ROOT / name
                    data = read_plain_file(path)
                    saved = stage / name
                    saved.parent.mkdir(parents=True, exist_ok=True)
                    saved.write_bytes(data)
                    files[name] = "100755" if path.stat().st_mode & 0o100 else "100644"
                atomic_json(stage / "queue.json", {"subject": subject, "files": files})
                event = f"{time.time_ns()}-{stage.name}"
                stage.rename(pending / event)
            note.rename(archive / f"{event}.txt")
            report(f"Captured {note.name}: {subject}")
        except (RuntimeError, OSError, UnicodeError) as error:
            result = {"state": "invalid", "note": note.name, "diagnostics": [str(error)]}
            atomic_json(state / "candidate.json", result)
            note.rename(archive / f"{time.time_ns()}-invalid.txt")
            report(f"Invalid handoff {note.name}: {error}")


def read_bundle(event):
    item = json.loads(read_plain_file(event / "queue.json"))
    check_subject(item["subject"])
    files = {}
    for path, mode in item["files"].items():
        check_queue_path(path)
        if mode is None:
            files[path] = None
        elif mode in ("100644", "100755"):
            files[path] = read_plain_file(event / path)
        else:
            raise RuntimeError(f"Invalid queued file mode for {path!r}")
    digest = sha256(json.dumps(item, sort_keys=True).encode() + sources_digest(
        {name: data for name, data in files.items() if data is not None}
    ).encode()).hexdigest()
    return item, files, digest


def move_event(state, event, destination):
    folder = state / destination
    folder.mkdir(exist_ok=True)
    event.rename(folder / event.name)


def audit_pending(state):
    """B checks a candidate against the exact Lean sources exported by C."""
    events = sorted((state / "pending").glob("*"))
    pointer = state / "base.json"
    if not events or any((state / "verified").glob("*")):
        return
    if not pointer.exists():
        atomic_json(state / "candidate.json", {"state": "waiting-for-publication-base", "event": events[0].name})
        return
    base = json.loads(read_plain_file(pointer))
    parent = base["parent"]
    if not re.fullmatch(r"[0-9a-f]{40,64}", parent):
        raise RuntimeError("Invalid publication base")
    sources = worktree_sources(state / "bases" / parent)
    if sources_digest(sources) != base["digest"]:
        raise RuntimeError("Publication base snapshot has changed")
    event = events[0]
    item, files, bundle_digest = read_bundle(event)
    for name, data in files.items():
        if proof_path(name):
            if data is None:
                sources.pop(name, None)
            else:
                sources[name] = data
    result = audited_snapshot(state, sources, state / "candidate.json") | {
        "parent": parent, "bundle": bundle_digest, "subject": item["subject"], "event": event.name,
    }
    atomic_json(state / "candidate.json", result)
    atomic_json(event / "build-receipt.json", result)
    move_event(state, event, "verified" if result["state"] == "passed" else "rejected")


def publisher_repo(state):
    repo = state / "publisher"
    with lock(state / "publisher-init.lock"):
        if not repo.exists():
            with tempfile.TemporaryDirectory(dir=state, prefix="publisher-") as tmp:
                clone = Path(tmp) / "repo"
                git(ROOT, "clone", "--quiet", "--no-checkout", "--no-hardlinks", "--", str(ROOT), str(clone))
                for key in ("user.name", "user.email"):
                    git(clone, "config", key, git(ROOT, "config", key).decode().strip())
                remote = git(ROOT, "remote", "get-url", "--push", "origin").decode().strip()
                uri = urlsplit(remote)
                if uri.scheme in ("http", "https") and uri.username is not None:
                    raise RuntimeError("Configure origin without credentials embedded in its URL")
                if not uri.scheme and Path(remote).exists():
                    remote = str(Path(remote).resolve())
                git(clone, "remote", "set-url", "origin", remote)
                git(clone, "update-ref", "refs/moc/base", "HEAD")
                clone.rename(repo)
    return repo


def tree_sources(repo, parent):
    entries = git(repo, "ls-tree", "-r", "-z", parent, "--", "Lean").decode().split("\0")
    sources = {}
    for entry in filter(None, entries):
        record, name = entry.split("\t", 1)
        if build_path(name):
            mode, kind, oid = record.split()
            if mode not in ("100644", "100755") or kind != "blob":
                raise RuntimeError(f"Lean proof sources must be regular files: {name}")
            sources[name] = git(repo, "cat-file", "blob", oid)
    return sources


def publish_base(state, repo, parent):
    """C exports a read-only input for B without giving B repository access."""
    root = state / "bases"
    root.mkdir(exist_ok=True)
    destination = root / parent
    sources = tree_sources(repo, parent)
    if not destination.exists():
        with tempfile.TemporaryDirectory(dir=root, prefix="base-") as tmp:
            project = Path(tmp)
            sync_snapshot(project, sources)
            project.rename(destination)
    atomic_json(state / "base.json", {"parent": parent, "digest": sources_digest(sources)})


def process_commit(state, repo, event):
    """C commits the exact candidate approved by B. No compilation occurs here."""
    item, files, bundle_digest = read_bundle(event)
    checked = json.loads(read_plain_file(event / "build-receipt.json"))
    if checked["state"] != "passed" or checked["bundle"] != bundle_digest:
        report(f"Rejected {event.name}: candidate does not match the build receipt")
        move_event(state, event, "rejected")
        return
    parent = git(repo, "rev-parse", "HEAD").decode().strip()
    git(repo, "read-tree", parent)
    for path, mode in item["files"].items():
        if mode is None:
            git(repo, "update-index", "--force-remove", "--", path)
        else:
            oid = git(repo, "hash-object", "-w", "--stdin", data=files[path]).decode().strip()
            git(repo, "update-index", "--add", "--cacheinfo", f"{mode},{oid},{path}")
    tree = git(repo, "write-tree").decode().strip()
    result = checked | {"tree": tree}
    same_tree = tree == git(repo, "rev-parse", f"{parent}^{{tree}}").decode().strip()
    if same_tree:
        result.update(commit=parent, unchanged=True)
        report(f"Already applied {event.name}")
    elif checked["parent"] != parent:
        publish_base(state, repo, parent)
        move_event(state, event, "pending")
        report(f"Returned {event.name} to B: publication base changed")
        return
    elif checked["digest"] != sources_digest(tree_sources(repo, tree)):
        move_event(state, event, "rejected")
        report(f"Rejected {event.name}: Lean tree does not match the build receipt")
        return
    else:
        commit = git(repo, "commit-tree", tree, "-p", parent, "-m", item["subject"]).decode().strip()
        git(repo, "update-ref", "HEAD", commit, parent)
        result.update(commit=commit)
        publish_base(state, repo, commit)
        report(f"Committed {commit[:12]}: {item['subject']}")
    atomic_json(event / "receipt.json", result)
    move_event(state, event, "committed")


def commit_pending(state, once):
    with lock(state / "commit.lock", wait=False):
        repo = publisher_repo(state)
        publish_base(state, repo, git(repo, "rev-parse", "HEAD").decode().strip())
        while True:
            for event in sorted((state / "verified").glob("*")):
                process_commit(state, repo, event)
            if once:
                return 0
            time.sleep(1)


def require_publication_remote(repo):
    remote = git(repo, "remote", "get-url", "--push", "origin").decode().strip()
    if remote.removesuffix(".git") != PUBLISH_URL:
        raise RuntimeError(f"Publication requires {PUBLISH_URL}")


def push_batches(state, branch, batch, once, flush):
    with lock(state / "push.lock", wait=False):
        repo = publisher_repo(state)
        if branch != PUBLISH_BRANCH:
            raise RuntimeError(f"Publication requires {PUBLISH_BRANCH}")
        require_publication_remote(repo)
        previous = f"refs/moc/published/{branch}"
        marker = flush_marker(state, branch)
        while True:
            revision = git(repo, "rev-parse", "--verify", "--quiet", previous, check=False)
            base = revision.decode().strip() or "refs/moc/base"
            commits = git(repo, "rev-list", "--first-parent", "--reverse", f"{base}..HEAD").decode().split()
            drained = not any(
                item for folder in ("intents", "pending", "verified")
                for item in (state / folder).glob("*.txt" if folder == "intents" else "*")
            )
            forced = flush or (drained and marker.exists())
            if commits and (len(commits) >= batch or forced):
                tip = commits[min(batch, len(commits)) - 1]
                report(f"Pushing {min(batch, len(commits))} audited commits through {tip[:12]} to {branch}")
                try:
                    git(repo, "push", "origin", f"{tip}:refs/heads/{branch}")
                except subprocess.CalledProcessError:
                    if once:
                        return 1
                    time.sleep(15)
                    continue
                git(repo, "update-ref", previous, tip)
                continue
            if drained and not commits:
                marker.unlink(missing_ok=True)
            if once:
                return 0
            time.sleep(1)


def flush_marker(state, branch):
    return state / f"flush-{sha256(branch.encode()).hexdigest()}"


def flush_for_merge(state):
    def require_workers():
        if not (state / "base.json").is_file():
            raise RuntimeError("The publication worker has not exported a base")
        for name in ("watch", "commit", "push"):
            path = state / f"{name}.process.lock"
            if path.is_file():
                with path.open("r") as handle:
                    try:
                        fcntl.flock(handle, fcntl.LOCK_EX | fcntl.LOCK_NB)
                    except BlockingIOError:
                        continue
            raise RuntimeError(f"The {name} worker must be running to drain the queue")

    require_workers()
    marker = flush_marker(state, PUBLISH_BRANCH)
    marker.touch()
    report("Waiting for the Lean handoff queue to drain and the final batch to push")
    while marker.exists():
        require_workers()
        time.sleep(1)


def merge_verified(state):
    """Drain the audited queue and integrate the published branch into origin/main."""
    if (state / "base.json").is_file():
        flush_for_merge(state)
    else:
        report("The publication base is absent. Publishing the commits already verified by the worker.")
        if push_batches(state, PUBLISH_BRANCH, batch=5, once=True, flush=True):
            raise RuntimeError(f"Could not push the audited commits to {PUBLISH_BRANCH}")
    repo = publisher_repo(state)
    require_publication_remote(repo)
    verified = git(repo, "rev-parse", "--verify", f"refs/moc/published/{PUBLISH_BRANCH}").decode().strip()
    git(repo, "fetch", "--no-tags", "origin",
        "+refs/heads/main:refs/remotes/origin/main",
        f"+refs/heads/{PUBLISH_BRANCH}:refs/remotes/origin/{PUBLISH_BRANCH}")
    remote_verified = git(repo, "rev-parse", f"refs/remotes/origin/{PUBLISH_BRANCH}").decode().strip()
    if remote_verified != verified:
        raise RuntimeError("The remote proof branch differs from the worker's published revision")
    main = git(repo, "rev-parse", "refs/remotes/origin/main").decode().strip()
    ancestor = git(repo, "merge-base", main, verified).decode().strip()
    if ancestor == verified:
        report(f"origin/main already contains {PUBLISH_BRANCH} at {verified[:12]}")
        return
    tip = verified
    if ancestor != main:
        try:
            tree = git(repo, "merge-tree", "--write-tree", main, verified).decode().strip()
        except subprocess.CalledProcessError as error:
            detail = (error.stdout or b"").decode(errors="replace").strip()
            raise RuntimeError(f"Cannot merge origin/main and {PUBLISH_BRANCH}\n{detail}") from error
        if tree_sources(repo, tree) != tree_sources(repo, verified):
            raise RuntimeError("The merged Lean sources differ from the audited branch and need a new audit")
        tip = git(repo, "commit-tree", tree, "-p", main, "-p", verified,
                  "-m", "merge: integrate verified Lean results").decode().strip()
    git(repo, "push", "origin", f"{tip}:refs/heads/main")
    report(f"Published {tip[:12]} to origin/main")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--state", type=Path, default=ROOT / "Lean" / ".lake" / "worker")
    commands = parser.add_subparsers(dest="command", required=True)
    for command in ("watch", "commit", "push"):
        sub = commands.add_parser(command)
        sub.add_argument("--once", action="store_true")
    push = commands.choices["push"]
    push.add_argument("--branch", choices=[PUBLISH_BRANCH], default=PUBLISH_BRANCH)
    push.add_argument("--batch", type=int, choices=range(5, 31), metavar="5..30", default=5)
    push.add_argument("--flush", action="store_true", help="Also publish a final batch smaller than --batch")
    commands.add_parser("flush").add_argument("--branch", choices=[PUBLISH_BRANCH], default=PUBLISH_BRANCH)
    commands.add_parser("merge", help="Drain verified work, merge into origin/main, and push")
    args = parser.parse_args()
    state = args.state.resolve()
    state.mkdir(parents=True, exist_ok=True)
    try:
        if args.command == "watch":
            return watch(state, args.once)
        if args.command == "commit":
            return commit_pending(state, args.once)
        if args.command == "push":
            return push_batches(state, args.branch, args.batch, args.once, args.flush)
        if args.command == "flush":
            flush_marker(state, args.branch).touch()
        if args.command == "merge":
            merge_verified(state)
    except (RuntimeError, OSError, subprocess.CalledProcessError) as error:
        report(f"lean_worker: {error}")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())

#!/usr/bin/env python3
"""Compile stable Lean snapshots and publish explicitly queued, checked changes."""

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
PINNED = ("lean-toolchain", "lakefile.toml", "lake-manifest.json")
GIT_PATH_ENV = {
    "GIT_DIR", "GIT_COMMON_DIR", "GIT_WORK_TREE", "GIT_INDEX_FILE",
    "GIT_OBJECT_DIRECTORY", "GIT_ALTERNATE_OBJECT_DIRECTORIES", "GIT_NAMESPACE", "GIT_SHALLOW_FILE",
}
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
  let mut count := 0
  for (name, decl) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    unless (`MOC).isPrefixOf env.allImportedModuleNames[idx.toNat]! do continue
    if decl.isUnsafe then continue
    count := count + 1
    let axioms ← collectAxioms name
    let extra := axioms.filter fun a => !allowed.contains a
    unless extra.isEmpty do
      throwError "{name} depends on unapproved axioms {extra}"
    let type := decl.type
    if type.isConstOf ``MOC.MOCIsTrue ||
        (type.isForall && type.bindingDomain!.isConstOf ``Nat) then
      if ← liftTermElabM (isDefEq type (mkConst ``MOC.MOCIsTrue)) then
        logInfo m!"MOC_WORKER_UNRESTRICTED_VERIFIED {name} {axioms}"
  if count == 0 then
    throwError "The MOC worker audit found no declarations"
  logInfo m!"MOC_WORKER_AUDITED {count} safe declarations"
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
        ["git", "-C", str(cwd), *args],
        env={key: value for key, value in os.environ.items() if key not in GIT_PATH_ENV},
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
        "README.md", "Lean/README.md", "Code/lean-workflow.sh", "Code/lean_worker.py", "Code/lean_fix.py"
    } or (name.parts[0] == "Docs" and name.suffix == ".md"):
        return raw
    raise RuntimeError(f"Path is outside Lean workflow publication scope: {raw!r}")


def worktree_sources():
    lean = ROOT / "Lean"
    files = [lean / name for name in (*PINNED, "MOC.lean")]
    files.extend(p for p in (lean / "MOC").rglob("*.lean") if proof_path(p.relative_to(ROOT).as_posix()))
    return {p.relative_to(ROOT).as_posix(): read_plain_file(p) for p in files}


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


def build(state, project, sources, log):
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
    env = os.environ | {"LEAN_NUM_THREADS": str(len(cores))}
    env.pop("LEAN_PATH", None)
    env.pop("LEAN_SRC_PATH", None)
    commands = [
        ["lake", "--no-cache", "build", *[f"+{module}" for module in modules]],
        ["lake", "env", "lean", f"-j{len(cores)}", audit_file],
    ]
    log.parent.mkdir(parents=True, exist_ok=True)
    with lock(state / "build.lock"), log.open("wb") as out:
        audit_offset = 0
        for index, command in enumerate(commands):
            out.write((f"$ taskset -c {cpu_list} {' '.join(command)}\n").encode())
            out.flush()
            audit_offset = out.tell()
            result = subprocess.run(
                ["taskset", "-c", cpu_list, *command],
                cwd=lean, env=env, stdout=out, stderr=subprocess.STDOUT,
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


def watch(state, once):
    with lock(state / "watch.lock", wait=False):
        last = None
        while True:
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
                data = {"digest": digest}
                sandbox = state / "watch" / "project"
                log = state / "logs" / f"watch-{digest}.log"
                report(f"Building {digest[:12]}: {log}")
                atomic_json(state / "status.json", data | {"state": "building", "log": str(log)})
                success, proofs = build(state, sandbox, sources, log)
                if not success:
                    failures = state / "failures"
                    failures.mkdir(exist_ok=True)
                    event = failures / digest
                    if not event.exists():
                        scratch = Path(tempfile.mkdtemp(dir=failures, prefix=".failure-"))
                        sync_snapshot(scratch / "project", sources)
                        shutil.copyfile(log, scratch / "build.log")
                        atomic_json(scratch / "failure.json", data | {
                            "files": sorted(p for p in sources if proof_path(p)),
                        })
                        scratch.rename(event)
                    log = event / "build.log"
                result = "passed" if success else "failed"
                atomic_json(state / "status.json", data | {
                    "state": result, "log": str(log), "unrestricted": proofs,
                })
                report(f"Build {result} for {digest[:12]}: {log}")
                last = digest
                if once:
                    return 0 if success else 1
            time.sleep(1)


def enqueue(state, subject, paths):
    if not subject.strip() or "\n" in subject or "\r" in subject:
        raise RuntimeError("Provide a one-line commit subject")
    paths = sorted({check_queue_path(path) for path in paths})
    pending = state / "pending"
    pending.mkdir(exist_ok=True)
    with lock(state / "enqueue.lock"):
        with tempfile.TemporaryDirectory(dir=state, prefix="enqueue-") as tmp:
            bundle = Path(tmp)
            files = {}
            for name in paths:
                path = ROOT / name
                if not path.exists() and not path.is_symlink():
                    git(ROOT, "ls-files", "--error-unmatch", "--", name)
                    files[name] = None
                    continue
                data = read_plain_file(path)
                saved = bundle / name
                saved.parent.mkdir(parents=True, exist_ok=True)
                saved.write_bytes(data)
                files[name] = "100755" if path.stat().st_mode & 0o100 else "100644"
            atomic_json(bundle / "queue.json", {"subject": subject, "files": files})
            event = pending / f"{time.time_ns()}-{bundle.name}"
            bundle.rename(event)
    report(f"Queued {event.name}: {subject}")


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


def process_commit(state, repo, event):
    item = json.loads((event / "queue.json").read_text())
    parent = git(repo, "rev-parse", "HEAD").decode().strip()
    git(repo, "read-tree", parent)
    for path, mode in item["files"].items():
        check_queue_path(path)
        if mode is None:
            git(repo, "update-index", "--force-remove", "--", path)
        else:
            if mode not in ("100644", "100755"):
                raise RuntimeError(f"Invalid queued file mode for {path!r}")
            blob = read_plain_file(event / path)
            oid = git(repo, "hash-object", "-w", "--stdin", data=blob).decode().strip()
            git(repo, "update-index", "--add", "--cacheinfo", f"{mode},{oid},{path}")
    tree = git(repo, "write-tree").decode().strip()
    log = state / "logs" / f"queue-{event.name}.log"
    result = {"parent": parent, "tree": tree, "log": str(log), "subject": item["subject"]}
    state_name = "committed"
    if tree != git(repo, "rev-parse", f"{parent}^{{tree}}").decode().strip():
        report(f"Auditing queued commit {event.name}: {log}")
        success, proofs = build(state, state / "commit" / "project", tree_sources(repo, tree), log)
        if success:
            commit = git(repo, "commit-tree", tree, "-p", parent, "-m", item["subject"]).decode().strip()
            git(repo, "update-ref", "HEAD", commit, parent)
            result.update(commit=commit, unrestricted=proofs)
            report(f"Committed {commit[:12]}: {item['subject']}")
        else:
            state_name = "rejected"
            report(f"Rejected {event.name}: {log}")
    else:
        result.update(commit=parent, unchanged=True)
        report(f"Already applied {event.name}")
    atomic_json(event / "receipt.json", result)
    (state / state_name).mkdir(exist_ok=True)
    event.rename(state / state_name / event.name)
    return state_name == "committed"


def commit_pending(state, once):
    with lock(state / "commit.lock", wait=False):
        repo = publisher_repo(state)
        failure = False
        while True:
            for event in sorted((state / "pending").glob("*")):
                failure = not process_commit(state, repo, event) or failure
            if once:
                return int(failure)
            time.sleep(1)


def push_batches(state, branch, batch, once, flush):
    with lock(state / "push.lock", wait=False):
        repo = publisher_repo(state)
        git(repo, "check-ref-format", f"refs/heads/{branch}")
        previous = f"refs/moc/published/{branch}"
        marker = flush_marker(state, branch)
        while True:
            revision = git(repo, "rev-parse", "--verify", "--quiet", previous, check=False)
            base = revision.decode().strip() or "refs/moc/base"
            commits = git(repo, "rev-list", "--first-parent", "--reverse", f"{base}..HEAD").decode().split()
            drained = not any((state / "pending").glob("*"))
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


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--state", type=Path, default=ROOT / "Lean" / ".lake" / "worker")
    commands = parser.add_subparsers(dest="command", required=True)
    for command in ("watch", "commit", "push"):
        sub = commands.add_parser(command)
        sub.add_argument("--once", action="store_true")
    add = commands.add_parser("enqueue")
    add.add_argument("subject")
    add.add_argument("paths", nargs="+")
    push = commands.choices["push"]
    push.add_argument("--branch", default="moc-verified")
    push.add_argument("--batch", type=int, choices=range(5, 31), metavar="5..30", default=5)
    push.add_argument("--flush", action="store_true", help="Also publish a final batch smaller than --batch")
    commands.add_parser("flush").add_argument("--branch", default="moc-verified")
    args = parser.parse_args()
    state = args.state.resolve()
    state.mkdir(parents=True, exist_ok=True)
    try:
        if args.command == "watch":
            return watch(state, args.once)
        if args.command == "enqueue":
            enqueue(state, args.subject, args.paths)
        if args.command == "commit":
            return commit_pending(state, args.once)
        if args.command == "push":
            return push_batches(state, args.branch, args.batch, args.once, args.flush)
        if args.command == "flush":
            git(ROOT, "check-ref-format", f"refs/heads/{args.branch}")
            flush_marker(state, args.branch).touch()
    except (RuntimeError, OSError, subprocess.CalledProcessError) as error:
        report(f"lean_worker: {error}")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())

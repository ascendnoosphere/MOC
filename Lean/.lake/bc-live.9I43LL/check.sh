#!/usr/bin/env bash
set -euo pipefail
origin_root=$1
tmp=$2
export PATH="/tmp/moc-toolchain/lean-4.19.0-linux/bin:$PATH"
export MOC_LEAN_WORKER_STATE="$tmp/state" GIT_ALLOW_PROTOCOL=file
export GIT_CONFIG_NOSYSTEM=1 GIT_CONFIG_GLOBAL=/dev/null GIT_TERMINAL_PROMPT=0
unset GIT_CONFIG_COUNT MOC_LEAN_PUSH_BATCH
export GIT_AUTHOR_NAME="fixture" GIT_COMMITTER_NAME="fixture"
export GIT_AUTHOR_EMAIL="fixture@example.invalid" GIT_COMMITTER_EMAIL="fixture@example.invalid"
state=$MOC_LEAN_WORKER_STATE
work="$tmp/checkout"
remote="$tmp/remote"
mkdir -p "$work/Code" "$state/intents"
git -C "$origin_root" archive HEAD Lean | tar -x -C "$work"
cp -- "$origin_root"/Code/lean-{build,publish,workflow}.sh "$origin_root"/Code/lean_worker.py "$work/Code/"
mkdir -p "$work/Lean/.lake"
printf 'Preparing isolated Mathlib cache\n'
cp -a --reflink=auto "$origin_root/Lean/.lake/packages" "$work/Lean/.lake/"
git -C "$work" init -q -b main
git -C "$work" config user.name "Fixture"
git -C "$work" config user.email "fixture@example.invalid"
git -C "$work" add Lean
git -C "$work" commit -qm "fixture: verified repository baseline"
base=$(git -C "$work" rev-parse HEAD)
git init --bare -q "$remote"
git -C "$work" remote add origin "$remote"
cd "$work"
cleanup() {
  if [[ -f "$state/watch.pid" ]]; then
    bash Code/lean-workflow.sh stop watch commit push || true
  fi
}
trap cleanup EXIT
bash Code/lean-publish.sh commit --once
if bash Code/lean-publish.sh push --once >"$tmp/guard.log" 2>&1; then
  printf 'Production publisher accepted a local URL unexpectedly\n' >&2
  exit 1
fi
rg -F 'Publication requires https://github.com/ascendnoosphere/MOC on moc-verified' "$tmp/guard.log"
sed -i "s|^PUBLISH_URL = .*|PUBLISH_URL = \"$remote\"|" Code/lean_worker.py
bash Code/lean-workflow.sh start --publish
cp "$state/watch.pid" "$tmp/original-watch.pid"
bash Code/lean-workflow.sh start --publish
cmp "$state/watch.pid" "$tmp/original-watch.pid"
if bash Code/lean-build.sh watch --once >"$tmp/duplicate.log" 2>&1; then
  printf 'A second build watcher unexpectedly started\n' >&2
  exit 1
fi
rg -F 'Another worker holds watch.lock' "$tmp/duplicate.log"

wait_for() {
  local label=$1
  shift
  local deadline=$((SECONDS + 240))
  until "$@"; do
    if ((SECONDS >= deadline)); then
      printf 'Timed out waiting on %s\n' "$label" >&2
      tail -20 "$state"/{watch,commit,push}.log >&2 || true
      exit 1
    fi
    sleep 1
  done
}
draft_passed() {
  [[ -r "$state/status.json" ]] && rg -q '"state": "passed"' "$state/status.json"
}
receipt_contains() {
  local box=$1 subject=$2
  [[ -d "$state/$box" ]] && rg -q --glob 'build-receipt.json' -F "$subject" "$state/$box"
}
remote_has() {
  [[ $(git -C "$remote" rev-list --count "$base..refs/heads/moc-verified" 2>/dev/null) == "$1" ]]
}
remote_empty() {
  ! git -C "$remote" show-ref --verify --quiet refs/heads/moc-verified
}
submit() {
  local item=$1
  shift
  printf '%s\n' "$@" > "$state/intents/$item.tmp"
  mv "$state/intents/$item.tmp" "$state/intents/$item.txt"
}
rejected_for() {
  local subject=$1 diagnostic=$2
  local receipt
  receipt=$(rg -l --glob build-receipt.json -F "$subject" "$state/rejected")
  rg -q -F "$diagnostic" "$receipt"
}
wait_for "passing baseline build" draft_passed
printf 'Baseline built and audited\n'
cat > Lean/MOC/WorkflowSmoke.lean <<'LEAN'
namespace MOC
theorem workflowSmoke : False := by
  exact True.intro
end MOC
LEAN
submit broken "lean: fixture type error" Lean/MOC/WorkflowSmoke.lean
wait_for "real compiler rejection" receipt_contains rejected "lean: fixture type error"
rejected_for "lean: fixture type error" "type mismatch"
cat > Lean/MOC/WorkflowSmoke.lean <<'LEAN'
namespace MOC
theorem workflowSmoke : False := by
  sorry
end MOC
LEAN
submit admitted "lean: fixture admitted proof" Lean/MOC/WorkflowSmoke.lean
wait_for "admission rejection" receipt_contains rejected "lean: fixture admitted proof"
rejected_for "lean: fixture admitted proof" "uses 'sorry'"
cat > Lean/MOC/WorkflowSmoke.lean <<'LEAN'
namespace MOC
axiom workflowSmoke : False
end MOC
LEAN
submit axiom "lean: fixture custom axiom" Lean/MOC/WorkflowSmoke.lean
wait_for "custom axiom rejection" receipt_contains rejected "lean: fixture custom axiom"
rejected_for "lean: fixture custom axiom" "unapproved axioms"
test "$(git -C "$state/publisher" rev-parse HEAD)" = "$base"
remote_empty
printf 'Compiler error, sorry, and custom axiom all rejected\n'
cat > Lean/MOC/WorkflowSmoke.lean <<'LEAN'
namespace MOC
theorem workflowSmoke : (29 : Nat) + 13 = 42 := rfl
end MOC
LEAN
submit passing "lean: preserve the fixture proof subject" Lean/MOC/WorkflowSmoke.lean
wait_for "audited local proof commit" receipt_contains committed "lean: preserve the fixture proof subject"
matching_draft() {
  python3 -B - "$state" <<'PY'
import json, pathlib, sys
state = pathlib.Path(sys.argv[1])
draft = json.loads((state / "status.json").read_text())
candidate = json.loads((state / "candidate.json").read_text())
sys.exit(not (draft["state"] == candidate["state"] == "passed"
              and draft["digest"] == candidate["digest"] and draft["log"] == candidate["log"]))
PY
}
wait_for "shared draft and candidate audit" matching_draft
proof_digest=$(python3 -B -c 'import json,sys; print(json.load(open(sys.argv[1]))["digest"])' "$state/status.json")
test "$(rg -c "^Building ${proof_digest:0:12}:" "$state/watch.log")" -eq 1
test "$(git -C "$state/publisher" log -1 --format=%an)" = "ascendnooshpere"
test "$(git -C "$state/publisher" log -1 --format=%s)" = "lean: preserve the fixture proof subject"
remote_empty
printf 'Verified commit preserves subject and author, with one real audit shared by B\n'
printf 'theorem unpublishedFixture : False := by exact True.intro\n' > Lean/MOC/UnqueuedFixture.lean
mkdir -p Docs
for index in {2..6}; do
  path="Docs/workflow-fixture-$index.md"
  printf 'Fixture %s\n' "$index" > "$path"
  submit "good-$index" "lean: fixture commit $index" "$path"
  wait_for "commit $index" receipt_contains committed "lean: fixture commit $index"
  if ((index < 5)); then remote_empty; fi
  if ((index == 5)); then wait_for "first five-commit push" remote_has 5; fi
done
remote_has 5
bash Code/lean-workflow.sh flush
wait_for "forced final one-commit push" remote_has 6
test "$(git -C "$work" rev-parse HEAD)" = "$base"
test "$(git -C "$remote" log -6 --format=%an refs/heads/moc-verified | sort -u)" = "ascendnooshpere"
test "$(git -C "$remote" show refs/heads/moc-verified:Lean/MOC/WorkflowSmoke.lean)" = "$(cat Lean/MOC/WorkflowSmoke.lean)"
if git -C "$remote" cat-file -e refs/heads/moc-verified:Lean/MOC/UnqueuedFixture.lean 2>/dev/null; then
  printf 'Unqueued draft reached the remote\n' >&2
  exit 1
fi
rg -F 'Pushing 5 audited commits' "$state/push.log"
rg -F 'Pushing 1 audited commits' "$state/push.log"
printf 'LIVE PASS: three failed candidates, six exact commits, push batches of five and one.\n'

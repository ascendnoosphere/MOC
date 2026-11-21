#!/usr/bin/env bash
set -euo pipefail

root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd -P)
state=${MOC_LEAN_WORKER_STATE:-"$root/Lean/.lake/worker"}
mkdir -p -- "$state"
state=$(cd -- "$state" && pwd -P)
<<<<<<< HEAD
export MOC_LEAN_WORKER_STATE=$state
batch=${MOC_LEAN_PUSH_BATCH:-5}
build=(bash "$root/Code/lean-build.sh")
publish=(bash "$root/Code/lean-publish.sh")
=======
branch=${MOC_LEAN_PUSH_BRANCH:-moc-verified}
batch=${MOC_LEAN_PUSH_BATCH:-5}
author=ascendnooshpere
worker=(python3 -B "$root/Code/lean_worker.py" --state "$state")
fixer=(python3 -B "$root/Code/lean_fix.py" --state-dir "$state")
>>>>>>> origin/main
cd -- "$root"

running() {
  ! flock --nonblock "$state/$1.process.lock" true
}

start_worker() {
  local name=$1 attempt launcher
  shift
  if running "$name"; then
    printf '%s already running\n' "$name"
    return
  fi
  nohup setsid flock --nonblock --no-fork "$state/$name.process.lock" bash -c '
    printf "%s\n" "$$" > "$1"
    shift
    exec "$@"
  ' _ "$state/$name.pid" "$@" </dev/null >>"$state/$name.log" 2>&1 &
  launcher=$!
  for attempt in {1..20}; do
    if running "$name" && [[ -s $state/$name.pid ]]; then
      printf '%s running. Log %s\n' "$name" "$state/$name.log"
      return
    fi
    kill -0 "$launcher" 2>/dev/null || break
    sleep 0.05
  done
  printf 'Could not start %s. Log %s\n' "$name" "$state/$name.log" >&2
  return 1
}

usage() {
  cat <<'HELP'
Usage
<<<<<<< HEAD
  Code/lean-workflow.sh start [--publish]
  Code/lean-workflow.sh status
  Code/lean-workflow.sh flush
  Code/lean-workflow.sh stop [watch|repair|commit|push]

Operators start the four-core build watcher and optionally the publication
workers. Authors write a one-line commit subject and the associated paths to
a .txt file in Lean/.lake/worker/intents/. Build results appear in status.json
and candidate.json. Publication uses origin/moc-verified in batches of five.
=======
  Code/lean-workflow.sh start [--repair] [--publish]
  Code/lean-workflow.sh status
  Code/lean-workflow.sh enqueue 'lean: precise change' <root-relative paths...>
  Code/lean-workflow.sh flush
  Code/lean-workflow.sh stop [watch|repair|commit|push]

Start runs the four-core build watcher. Add --repair for isolated diagnostic
patches and --publish for the verified commit and push consumers. Publication
uses origin/moc-verified in batches of five by default. Set MOC_LEAN_PUSH_BRANCH
or MOC_LEAN_PUSH_BATCH before starting to override those choices.
>>>>>>> origin/main
HELP
}

case ${1:-help} in
  start)
    shift
<<<<<<< HEAD
    enable_publish=false
    for option in "$@"; do
      case $option in
        --publish) enable_publish=true ;;
=======
    repair=false
    publish=false
    for option in "$@"; do
      case $option in
        --repair) repair=true ;;
        --publish) publish=true ;;
>>>>>>> origin/main
        *) usage >&2; exit 2 ;;
      esac
    done
    command -v lake >/dev/null || { printf 'Pinned lake is required on PATH\n' >&2; exit 1; }
<<<<<<< HEAD
    start_worker watch "${build[@]}" watch
    if "$enable_publish"; then
      start_worker commit "${publish[@]}" commit
      start_worker push "${publish[@]}" push --batch "$batch"
=======
    start_worker watch "${worker[@]}" watch
    if "$repair"; then
      start_worker repair "${fixer[@]}" --watch
    fi
    if "$publish"; then
      start_worker commit env GIT_AUTHOR_NAME="$author" GIT_COMMITTER_NAME="$author" "${worker[@]}" commit
      start_worker push "${worker[@]}" push --branch "$branch" --batch "$batch"
>>>>>>> origin/main
    fi
    ;;
  status)
    for name in watch repair commit push; do
      if running "$name"; then
        printf '%s running. Log %s\n' "$name" "$state/$name.log"
      else
        printf '%s stopped\n' "$name"
      fi
    done
<<<<<<< HEAD
    for receipt in status candidate; do
      if [[ -f $state/$receipt.json ]]; then
        printf '%s result\n' "$receipt"
        cat -- "$state/$receipt.json"
      fi
    done
=======
>>>>>>> origin/main
    ;;
  stop)
    shift
    if (($# == 0)); then set -- watch repair commit push; fi
    for name in "$@"; do
      case $name in
        watch|repair|commit|push) ;;
        *) usage >&2; exit 2 ;;
      esac
      if running "$name"; then
        read -r pid <"$state/$name.pid"
        if [[ $pid =~ ^[1-9][0-9]+$ ]]; then
          kill -TERM -- "-$pid"
        fi
      fi
    done
    ;;
<<<<<<< HEAD
  flush)
    exec "${publish[@]}" flush
=======
  enqueue)
    shift
    exec "${worker[@]}" enqueue "$@"
    ;;
  flush)
    exec "${worker[@]}" flush --branch "$branch"
>>>>>>> origin/main
    ;;
  help|-h|--help)
    usage
    ;;
  *)
    usage >&2
    exit 2
    ;;
esac

#!/usr/bin/env bash
set -euo pipefail

root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd -P)
state=${MOC_LEAN_WORKER_STATE:-"$root/Lean/.lake/worker"}
mkdir -p -- "$state"
state=$(cd -- "$state" && pwd -P)
export MOC_LEAN_WORKER_STATE=$state
batch=${MOC_LEAN_PUSH_BATCH:-5}
build=(bash "$root/Code/lean-build.sh")
publish=(bash "$root/Code/lean-publish.sh")
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
  Code/lean-workflow.sh start [--publish]
  Code/lean-workflow.sh status
  Code/lean-workflow.sh flush
  Code/lean-workflow.sh stop [watch|repair|commit|push]

Operators start the four-core build watcher and optionally the publication
workers. Authors write a one-line commit subject and the associated paths to
a .txt file in Lean/.lake/worker/intents/. Build results appear in status.json
and candidate.json. Publication uses origin/moc-verified in batches of five.
HELP
}

case ${1:-help} in
  start)
    shift
    enable_publish=false
    for option in "$@"; do
      case $option in
        --publish) enable_publish=true ;;
        *) usage >&2; exit 2 ;;
      esac
    done
    command -v lake >/dev/null || { printf 'Pinned lake is required on PATH\n' >&2; exit 1; }
    start_worker watch "${build[@]}" watch
    if "$enable_publish"; then
      start_worker commit "${publish[@]}" commit
      start_worker push "${publish[@]}" push --batch "$batch"
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
    for receipt in status candidate; do
      if [[ -f $state/$receipt.json ]]; then
        printf '%s result\n' "$receipt"
        cat -- "$state/$receipt.json"
      fi
    done
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
  flush)
    exec "${publish[@]}" flush
    ;;
  help|-h|--help)
    usage
    ;;
  *)
    usage >&2
    exit 2
    ;;
esac

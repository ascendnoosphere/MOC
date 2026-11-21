#!/usr/bin/env bash
set -euo pipefail

root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd -P)
state=${MOC_LEAN_WORKER_STATE:-"$root/Lean/.lake/worker"}
case ${1:-} in
  commit|merge)
    export GIT_AUTHOR_NAME=ascendnooshpere GIT_COMMITTER_NAME=ascendnooshpere
    ;;
  push|flush) ;;
  git)
    shift
    unset GIT_DIR GIT_COMMON_DIR GIT_WORK_TREE GIT_INDEX_FILE GIT_OBJECT_DIRECTORY
    unset GIT_ALTERNATE_OBJECT_DIRECTORIES GIT_NAMESPACE GIT_SHALLOW_FILE
    exec git "$@"
    ;;
  *) exit 2 ;;
esac
exec python3 -B "$root/Code/lean_worker.py" --state "$state" "$@"

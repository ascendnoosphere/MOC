#!/usr/bin/env bash
set -euo pipefail

root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd -P)
case ${1:-watch} in
  watch)
    if (($#)); then shift; fi
    exec python3 -B "$root/Code/lean_worker.py" --state "${MOC_LEAN_WORKER_STATE:-"$root/Lean/.lake/worker"}" watch "$@"
    ;;
  compile|audit)
    mode=$1
    cpus=$2
    shift 2
    [[ $cpus =~ ^[0-9]+(,[0-9]+){0,3}$ ]] || exit 2
    IFS=, read -ra cores <<< "$cpus"
    ((${#cores[@]} >= 1 && ${#cores[@]} <= 4)) || exit 2
    export LEAN_NUM_THREADS=${#cores[@]}
    unset LEAN_PATH LEAN_SRC_PATH
    if [[ $mode == compile ]]; then
      exec taskset -c "$cpus" lake --no-cache build "$@"
    fi
    exec taskset -c "$cpus" lake env lean "-j$LEAN_NUM_THREADS" "$@"
    ;;
  *) exit 2 ;;
esac

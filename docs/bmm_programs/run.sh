#!/usr/bin/env bash
# run.sh — runs one step of the computation for one group without straining the machine: niced, with the number
# of threads, the memory cap and the heap-size hint of the group file (fields `threads`, `memory`, `heap`; defaults 1,
# 6G, and a --heap-size-hint of 4G, or 7G with threads; the environment variables THREADS, MEMMAX and HEAP override
# them), in the Julia environment of this folder (Project.toml, Manifest.toml: run
# julia --project=. -e 'import Pkg; Pkg.instantiate()' once), under systemd-run when it is available.  The program
# writes its own record GNN/N_name.txt; run.sh adds a last line "# <date>  exit code N" if the program left none.
#
#   ./run.sh G20              the proof for G20 (julia programs/bmm_proof.jl G20)        -> G20/3_bmm_proof.txt
#   ./run.sh G20 all          every step of the group, in the order of its group file (field `steps`;
#                             default: bfs modular proof traces orders)
#   ./run.sh G20 modular      one step;      ./run.sh all [step]     every group G4 .. G34 in turn
#   ./run.sh G31 bfs --order=53124   extra arguments are passed to the program (here: another ordering o)
#
# The steps, the same for every group (a group whose engine has no such step says so and exits with code 3):
#   bfs        programs/bfs_basis.jl        -> 1_bfs_basis.txt       the basis A and its coset table (modulo p)
#   modular    programs/zbasis_modular.jl   -> 2_zbasis_modular.txt  the candidate B and all tests modulo p
#   proof      programs/bmm_proof.jl        -> 3_bmm_proof.txt       the proof, exact
#   traces     programs/trace_values.jl     -> 4_trace_values.txt    values of the canonical trace
#   orders     programs/bfs_orders.jl       -> 5_bfs_orders.txt      all orderings o (the rows of Figure 2)
#
# Offline: nothing needs the internet once the environment is instantiated.  Resuming: a step cut short (reboot,
# out of memory) leaves a record without "exit code 0"; run it again (run_all.sh does so for every such record).
set -uo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")"
export JULIA_PKG_OFFLINE=true      # the package manager never tries the network
GROUPS_ALL="G4 G5 G6 G7 G8 G9 G10 G11 G12 G13 G14 G15 G16 G17 G18 G19 G20 G21 G22 G24 G25 G26 G27 G29 G31 G32 G33 G34"
[ $# -ge 1 ] || { sed -n "2,21p" "$0"; exit 1; }
target="$1"; steps0="${2:-proof}"; shift; [ $# -ge 1 ] && shift
[ "$target" = all ] && target="$GROUPS_ALL"

groupfile() {  # G4 -> G4/group04.toml; any other folder -> its group*.toml
  if [[ "$1" =~ ^G([0-9]+)$ ]]; then printf "%s/group%02d.toml" "$1" "${BASH_REMATCH[1]}"; else ls "$1"/group*.toml 2>/dev/null | head -1; fi; }
field() {      # field FILE NAME DEFAULT: the value of a scalar field of the group file (a number or a "string")
  local v; v=$(grep -E "^[[:space:]]*$2[[:space:]]*=" "$1" | head -1 | sed -E 's/^[^=]*=[[:space:]]*//; s/[[:space:]]*#.*$//; s/^"//; s/"$//')
  echo "${v:-$3}"
}
steps_of() {   # the list `steps = [...]` of the group file, default the five steps
  local v; v=$(grep -E "^[[:space:]]*steps[[:space:]]*=" "$1" | head -1 | sed -E 's/^[^=]*=//; s/#.*$//; s/[]["]//g; s/,/ /g')
  echo "${v:-bfs modular proof traces orders}"
}
program_of() { case "$1" in
  bfs) echo bfs_basis ;;      modular) echo zbasis_modular ;;    proof) echo bmm_proof ;;
  traces) echo trace_values ;; orders) echo bfs_orders ;;
  *) echo "run.sh: unknown step $1" >&2; exit 1 ;; esac; }
record_of() { case "$1" in
  bfs) echo 1_bfs_basis ;;    modular) echo 2_zbasis_modular ;;  proof) echo 3_bmm_proof ;;
  traces) echo 4_trace_values ;; orders) echo 5_bfs_orders ;; esac; }

launch() {  # launch MEM THREADS RECORD cmd...
  local mem=$1 thr=$2 rec=$3; shift 3
  if systemd-run --user --scope -q true 2>/dev/null; then
    JULIA_NUM_THREADS=$thr systemd-run --user --scope -q -p MemoryMax="$mem" nice -n 10 "$@"
  else
    JULIA_NUM_THREADS=$thr nice -n 10 "$@"
  fi
  local code=$?
  [ "$code" -eq 3 ] && [ ! -f "$rec" ] && return        # the engine has no such step: no record
  tail -1 "$rec" 2>/dev/null | grep -q "exit code" || echo "# $(date '+%F %T')  exit code $code" >> "$rec"
}

for g in $target; do
  f=$(groupfile "$g"); [ -f "$f" ] || { echo "run.sh: no group file $f" >&2; exit 1; }
  thr=${THREADS:-$(field "$f" threads 1)}; mem=${MEMMAX:-$(field "$f" memory 6G)}
  heap=${HEAP:-$(field "$f" heap "")}                       # --heap-size-hint: HEAP, the field heap, or the default
  [ -n "$heap" ] || heap=$([ "$thr" -gt 1 ] && echo 7G || echo 4G)
  steps="$steps0"; [ "$steps0" = all ] && steps=$(steps_of "$f")
  for step in $steps; do
    prog=$(program_of "$step") || exit 1; rec=$(record_of "$step")
    launch "$mem" "$thr" "$g/$rec.txt" julia --project=. --heap-size-hint=$heap "programs/$prog.jl" "$f" "$@"
  done
done

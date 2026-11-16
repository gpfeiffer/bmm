#!/usr/bin/env bash
# run_all.sh — produces every record of this folder: every step of every group (through run.sh), the small groups
# first, then G31, G33, G32; G34 is not included (its steps take 2 h, 30 h and 25 min and up to 13 GB of memory; run
# them by hand on a machine with 16 GB: ./run.sh G34 all, or ./run.sh G34 bfs, proof, traces).  One line per finished step is
# written to run_all.log.  The script can be stopped and started again: a step whose record already ends with
# "exit code 0" is skipped (and not mentioned in run_all.log) — so after a change of the programs, delete the records
# to be redone, or run ./run.sh all all.
cd "$(dirname "${BASH_SOURCE[0]}")"
steps_of() { v=$(grep -E "^[[:space:]]*steps[[:space:]]*=" "$1" | head -1 | sed -E 's/^[^=]*=//; s/#.*$//; s/[]["]//g; s/,/ /g'); echo "${v:-bfs modular proof traces orders}"; }
run() {   # run GROUP STEP
  rec=$(grep -E "^ *$2\)" run.sh | head -1 | sed -E 's/.*echo ([0-9]_[a-z0-9_]+).*/\1/')
  tail -1 "$1/$rec.txt" 2>/dev/null | grep -q "exit code 0" && return
  ./run.sh "$1" "$2" > /dev/null 2>&1
  echo "$(date '+%F %T')  $1 $2: $(tail -1 "$1/$rec.txt")" >> run_all.log
}
for g in G4 G12 G5 G8 G13 G6 G7 G14 G9 G10 G15 G11 G20 G22 G16 G24 G25 G26 G21 G17 G18 G27 G29 G19; do
  for step in bfs modular proof traces orders; do run "$g" "$step"; done
done
for g in G31 G33 G32; do for step in $(steps_of "$g/group${g#G}.toml"); do run "$g" "$step"; done; done
echo "$(date '+%F %T')  run_all.sh finished" >> run_all.log

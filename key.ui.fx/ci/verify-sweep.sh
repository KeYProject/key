#!/usr/bin/env bash
# Full per-flag UI regression sweep of key.ui.fx (WP-11 institutionalized as the nightly
# .github/workflows/ui-verify.yml). Sharded for CI parallelism: each shard runs its flags
# sequentially inside its own Xvfb display (one app at a time per shard), -Xmx6g, software
# rendering (prism.order=sw).
#
# Usage:
#   verify-sweep.sh            # run all shards sequentially (local full sweep)
#   verify-sweep.sh shard3 ... # run only the named shards (CI matrix job)
#
# Every flag is a public headless self-test hook (-Dkey.fx.verify.<flag>, whitelisted in
# key.ui.fx/build.gradle); each reports PASS/FAIL on stdout. A flag run "exhausts its budget"
# when the hook verified within the budget but the app stays open — the runner SIGTERMs it and
# the verdict is taken from the log afterwards (exit 143 / BUILD FAILED after the markers are
# the expected runner kill, not a failure).
set -u
export PATH="$HOME/.local/bin:$PATH"
W=$(cd "$(dirname "$0")/../.." && pwd)
EX=$W/key.ui/examples
AGATHA=$EX/firstTouch/01-Agatha/project.key
STRASSEN=$EX/standard_key/java_dl/strassen/strassen.auto.0.proof
NORM=$EX/standard_key/quantifiers/normalisation0.key
USEQ=$EX/standard_key/queries/useQuery.key
GCD=$W/key.core/src/test/resources/testcase/merge/gcd.mergePointStatements.key
OUT=${UI_VERIFY_OUT:-$W/build/ui-verify}
mkdir -p "$OUT/tmp"
: > "$OUT/RESULTS.md"
cd "$W"

start_display() {
  local log="$OUT/xvfb-$$.log"
  Xvfb :99 -screen 0 1920x1080x24 -nolisten tcp > "$log" 2>&1 &
  XVFB_PID=$!
  export DISPLAY=:99
  trap 'kill $XVFB_PID 2>/dev/null' EXIT
  for _ in $(seq 1 20); do
    sleep 0.5
    grep -aq 'Virtual framebuffer' "$log" 2>/dev/null && break
  done
}

run_flag() {
  local name="$1" budget="$2"; shift 2
  local log="$OUT/$name.log"
  pkill -f '[d]e.uka.ilkd.key.core.fx.MainEx' 2>/dev/null; sleep 2
  export JAVA_TOOL_OPTIONS="-Xmx6g -Dprism.order=sw -Djava.io.tmpdir=$OUT/tmp $*"
  ./gradlew --no-daemon --max-workers=1 :key.ui.fx:run > "$log" 2>&1 &
  local gpid=$! done=0
  for _ in $(seq 1 $((budget / 5))); do
    sleep 5
    if ! kill -0 "$gpid" 2>/dev/null; then done=1; break; fi
  done
  if [ "$done" -eq 0 ]; then
    echo "-- $name: budget end (expected unless the flag exits by itself)" >> "$OUT/RESULTS.md"
  else
    echo "-- $name: app exited on its own" >> "$OUT/RESULTS.md"
  fi
  sleep 2; pkill -f '[d]e.uka.ilkd.key.core.fx.MainEx' 2>/dev/null; sleep 1
}

summarize() {
  local name="$1"
  local count; count=$(grep -acE '(PASS|verification: OK)' "$OUT/$name.log" 2>/dev/null || echo 0)
  local hits; hits=$(grep -aE '(PASS|verification: OK)' "$OUT/$name.log" 2>/dev/null | tail -2 | sed 's/\x1b\[[0-9;]*m//g' | cut -c1-190)
  local fails; fails=$(grep -aE 'verification.*FAIL|verify.*FAIL|=FAIL|FAIL \(|Exception in thread' "$OUT/$name.log" 2>/dev/null | grep -av 'BUILD FAILED\|Task :key.ui.fx:run FAILED\|FAILURE:' | head -2 | sed 's/\x1b\[[0-9;]*m//g' | cut -c1-150)
  { echo "### $name (PASS-lines=$count)"; [ -n "$hits" ] && echo "$hits"; [ -n "$fails" ] && echo "FAIL-LINES:" && echo "$fails"; echo; } >> "$OUT/RESULTS.md"
  if [ "$count" -eq 0 ] || [ -n "$fails" ]; then
    echo "$name" >> "$OUT/failed-flags.txt"
  fi
}

finish() {
  for f in "$@"; do summarize "$f"; done
  echo "SWEEP COMPLETE (shards: ${SHARDS[*]})" >> "$OUT/RESULTS.md"
  if [ -s "$OUT/failed-flags.txt" ]; then
    echo "FAILED flags in ${SHARDS[*]}: $(paste -sd, "$OUT/failed-flags.txt")"
  else
    echo "UI verify sweep: all flags PASS (shards: ${SHARDS[*]})"
  fi
}

# --- shard 1: base views on the Agatha demo, part 1 (~30 min) -------------------
shard1() {
  for f in sequent tree goallist notifications docking help; do
    run_flag "$f" 300 "-Dkey.fx.verify.$f=1 -Dkey.fx.demo.sequent=$AGATHA"
  done
  finish sequent tree goallist notifications docking help
}

# --- shard 2: base views on the Agatha demo, part 2 (~35 min) -------------------
shard2() {
  for f in soundiness profileloading javacsettings termmenu colors shortcuts sequentmenu; do
    run_flag "$f" 300 "-Dkey.fx.verify.$f=1 -Dkey.fx.demo.sequent=$AGATHA"
  done
  # dialogs incl. the WP-9 contract E2E leg (runs within the dialogs hook)
  run_flag dialogs 420 "-Dkey.fx.verify.dialogs=1 -Dkey.fx.verify.dialogs.contract=1 -Dkey.fx.demo.sequent=$AGATHA"
  finish soundiness profileloading javacsettings termmenu colors shortcuts sequentmenu dialogs
}

# --- shard 3: live auto-mode interaction (~35 min) -------------------------------
shard3() {
  run_flag search 420 "-Dkey.fx.verify.search=andleft -Dkey.fx.demo.sequent=$AGATHA -Dkey.fx.demo.autoprove.live=1"
  run_flag sequentsearch 420 "-Dkey.fx.verify.sequentsearch=agatha -Dkey.fx.demo.sequent=$AGATHA -Dkey.fx.demo.autoprove.live=1"
  run_flag sequentsearchmodes 420 "-Dkey.fx.verify.sequentsearchmodes=1 -Dkey.fx.demo.sequent=$AGATHA -Dkey.fx.demo.autoprove.live=1"
  run_flag treefilters 420 "-Dkey.fx.verify.treefilters=1 -Dkey.fx.demo.sequent=$AGATHA -Dkey.fx.demo.autoprove.live=1"
  finish search sequentsearch sequentsearchmodes treefilters
}

# --- shard 4: special-demo flags (~40 min) ----------------------------------------
shard4() {
  run_flag tacletmatch 300 "-Dkey.fx.verify.tacletmatch=1 -Dkey.fx.demo.sequent=$AGATHA"
  run_flag inputfreeze 360 "-Dkey.fx.verify.inputfreeze=1 -Dkey.fx.demo.sequent=$AGATHA -Dkey.fx.demo.autoprove=1"
  run_flag updatehighlight 300 "-Dkey.fx.verify.updatehighlight=1 -Dkey.fx.demo.sequent=$USEQ"
  run_flag lemmaorigin 300 "-Dkey.fx.verify.lemmaorigin=1 -Dkey.fx.demo.sequent=$STRASSEN"
  run_flag joinmerge 300 "-Dkey.fx.verify.joinmerge=1 -Dkey.fx.demo.sequent=$AGATHA"
  run_flag joinmerge-gcd 300 "-Dkey.fx.verify.joinmerge=1 -Dkey.fx.verify.joinmerge.maxsteps= -Dkey.fx.demo.sequent=$GCD"
  run_flag proofmgmt-all 400 "-Dkey.fx.verify.proofmgmt=all -Dkey.fx.demo.sequent=$AGATHA"
  finish tacletmatch inputfreeze updatehighlight lemmaorigin joinmerge joinmerge-gcd proofmgmt-all
}

# --- shard 5: WP-1..WP-10 extension/view flags, part 1 (~40 min) ------------------
shard5() {
  run_flag extensions 420 "-Dkey.fx.verify.extensions=1 -Dkey.fx.demo.sequent=$AGATHA"
  run_flag exploration 420 "-Dkey.fx.verify.exploration=1 -Dkey.fx.demo.sequent=$AGATHA"
  run_flag caching 420 "-Dkey.fx.verify.caching=1 -Dkey.fx.demo.sequent=$AGATHA"
  run_flag prooftree 420 "-Dkey.fx.verify.prooftree=1 -Dkey.fx.demo.sequent=$AGATHA -Dkey.fx.demo.autoprove=1"
  run_flag slicing 420 "-Dkey.fx.verify.slicing=1 -Dkey.fx.demo.sequent=$AGATHA"
  run_flag testgen 420 "-Dkey.fx.verify.testgen=1 -Dkey.fx.demo.sequent=$AGATHA"
  finish extensions exploration caching prooftree slicing testgen
}

# --- shard 6: WP-1..WP-10 extension/view flags, part 2 (~40 min) ------------------
# themepersist save+restore must stay in one shard: the restore leg reads the preference
# persisted by the save leg.
shard6() {
  run_flag heatmap 420 "-Dkey.fx.verify.heatmap=1 -Dkey.fx.demo.sequent=$STRASSEN"
  run_flag isabelle 300 "-Dkey.fx.verify.isabelle=1 -Dkey.fx.demo.sequent=$NORM"
  run_flag sourceconsistency 300 "-Dkey.fx.verify.sourceconsistency=1"
  run_flag autosave 420 "-Dkey.fx.verify.autosave=1 -Dkey.fx.demo.sequent=$AGATHA"
  run_flag minimizeinteraction 420 "-Dkey.fx.verify.minimizeinteraction=1 -Dkey.fx.demo.sequent=$AGATHA"
  run_flag themepersist-s 300 "-Dkey.fx.verify.themepersist=save -Dkey.fx.demo.sequent=$AGATHA"
  run_flag themepersist-r 300 "-Dkey.fx.verify.themepersist=restore -Dkey.fx.demo.sequent=$AGATHA"
  finish heatmap isabelle sourceconsistency autosave minimizeinteraction themepersist-s themepersist-r
}

# --- shard 7: long/special runs (~45 min) ------------------------------------------
shard7() {
  # modal-dialog flag (needs key dismissal via XTEST/xdotool)
  pkill -f '[d]e.uka.ilkd.key.core.fx.MainEx' 2>/dev/null; sleep 2
  export JAVA_TOOL_OPTIONS="-Xmx6g -Dprism.order=sw -Djava.io.tmpdir=$OUT/tmp -Dkey.fx.verify.profileloadingdialog=1 -Dkey.fx.demo.sequent=$AGATHA"
  ./gradlew --no-daemon --max-workers=1 :key.ui.fx:run > "$OUT/profileloadingdialog.log" 2>&1 &
  GPID=$!
  sleep 40; xdotool key Return 2>/dev/null
  sleep 3; xdotool key Escape 2>/dev/null || true
  for _ in $(seq 1 72); do
    sleep 5
    if ! kill -0 "$GPID" 2>/dev/null; then break; fi
  done
  pkill -f '[d]e.uka.ilkd.key.core.fx.MainEx' 2>/dev/null; sleep 2

  # SMT with real z3 from keyproject/setup-smt; apply/undo round trip
  run_flag smt 900 "-Dkey.fx.verify.smt=1 -Dkey.fx.demo.sequent=$AGATHA"

  # loadingexit: app must terminate ITSELF with exit code 0 (no pkill allowed)
  pkill -f '[d]e.uka.ilkd.key.core.fx.MainEx' 2>/dev/null; sleep 2
  export JAVA_TOOL_OPTIONS="-Xmx6g -Dprism.order=sw -Djava.io.tmpdir=$OUT/tmp -Dkey.fx.verify.loadingexit=1"
  ./gradlew --no-daemon --max-workers=1 :key.ui.fx:run > "$OUT/loadingexit.log" 2>&1 &
  GPID=$!; wait "$GPID"; rc=$?
  echo "loadingexit exit-code=$rc" >> "$OUT/RESULTS.md"
  if [ "$rc" -ne 0 ]; then echo "loadingexit" >> "$OUT/failed-flags.txt"; fi

  # harness-only flags
  for f in proofdiff drawer drawerlayout rightclickmacro; do
    run_flag "$f" 300 "-Dkey.fx.verify.$f=1 -Dkey.fx.demo.sequent=$AGATHA"
  done
  finish profileloadingdialog smt loadingexit proofdiff drawer drawerlayout rightclickmacro
}

# --- main --------------------------------------------------------------------------
: > "$OUT/failed-flags.txt"
start_display
if [ $# -eq 0 ]; then
  SHARDS=(shard1 shard2 shard3 shard4 shard5 shard6 shard7)
else
  SHARDS=("$@")
fi
for s in "${SHARDS[@]}"; do
  echo "== $s" >> "$OUT/RESULTS.md"
  "$s" || true
done
if [ -s "$OUT/failed-flags.txt" ]; then
  echo "::error::UI verify sweep failed flags: $(paste -sd, "$OUT/failed-flags.txt")"
  exit 1
fi

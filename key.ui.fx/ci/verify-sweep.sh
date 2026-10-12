#!/usr/bin/env bash
# Full per-flag UI regression sweep of key.ui.fx (WP-11 institutionalized as the
# .github/workflows/ui-verify.yml). The CI workflow runs ONE matrix job per flag (maximum
# parallelization); this script executes one or more named flags sequentially inside its own
# Xvfb display, -Xmx6g, software rendering (prism.order=sw). Without arguments it runs all
# flags sequentially (local full sweep).
#
# Usage:
#   verify-sweep.sh                  # all flags, sequential (local full sweep)
#   verify-sweep.sh sequent smt ...  # only the named flags (CI matrix job)
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

ALL_FLAGS=(sequent tree goallist notifications docking help soundiness profileloading
  javacsettings termmenu colors shortcuts sequentmenu dialogs search sequentsearch
  sequentsearchmodes treefilters tacletmatch inputfreeze updatehighlight lemmaorigin
  joinmerge joinmerge-gcd proofmgmt-all extensions exploration caching prooftree slicing
  testgen heatmap isabelle sourceconsistency autosave minimizeinteraction themepersist
  profileloadingdialog smt loadingexit proofdiff drawer drawerlayout rightclickmacro)

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

# name -> budget + JVM properties (the demo/verify recipe catalog)
flag_recipe() {
  case "$1" in
    sequent)             run_flag sequent 300 -Dkey.fx.verify.sequent=1 -Dkey.fx.demo.sequent=$AGATHA ;;
    tree)                run_flag tree 300 -Dkey.fx.verify.tree=1 -Dkey.fx.demo.sequent=$AGATHA ;;
    goallist)            run_flag goallist 300 -Dkey.fx.verify.goallist=1 -Dkey.fx.demo.sequent=$AGATHA ;;
    notifications)       run_flag notifications 300 -Dkey.fx.verify.notifications=1 -Dkey.fx.demo.sequent=$AGATHA ;;
    docking)             run_flag docking 300 -Dkey.fx.verify.docking=1 -Dkey.fx.demo.sequent=$AGATHA ;;
    help)                run_flag help 300 -Dkey.fx.verify.help=1 -Dkey.fx.demo.sequent=$AGATHA ;;
    soundiness)          run_flag soundiness 300 -Dkey.fx.verify.soundiness=1 -Dkey.fx.demo.sequent=$AGATHA ;;
    profileloading)      run_flag profileloading 300 -Dkey.fx.verify.profileloading=1 -Dkey.fx.demo.sequent=$AGATHA ;;
    javacsettings)       run_flag javacsettings 300 -Dkey.fx.verify.javacsettings=1 -Dkey.fx.demo.sequent=$AGATHA ;;
    termmenu)            run_flag termmenu 300 -Dkey.fx.verify.termmenu=1 -Dkey.fx.demo.sequent=$AGATHA ;;
    colors)              run_flag colors 300 -Dkey.fx.verify.colors=1 -Dkey.fx.demo.sequent=$AGATHA ;;
    shortcuts)           run_flag shortcuts 300 -Dkey.fx.verify.shortcuts=1 -Dkey.fx.demo.sequent=$AGATHA ;;
    sequentmenu)         run_flag sequentmenu 300 -Dkey.fx.verify.sequentmenu=1 -Dkey.fx.demo.sequent=$AGATHA ;;
    dialogs)             run_flag dialogs 420 -Dkey.fx.verify.dialogs=1 -Dkey.fx.verify.dialogs.contract=1 -Dkey.fx.demo.sequent=$AGATHA ;;
    search)              run_flag search 420 -Dkey.fx.verify.search=andleft -Dkey.fx.demo.sequent=$AGATHA -Dkey.fx.demo.autoprove.live=1 ;;
    sequentsearch)       run_flag sequentsearch 420 -Dkey.fx.verify.sequentsearch=agatha -Dkey.fx.demo.sequent=$AGATHA -Dkey.fx.demo.autoprove.live=1 ;;
    sequentsearchmodes)  run_flag sequentsearchmodes 420 -Dkey.fx.verify.sequentsearchmodes=1 -Dkey.fx.demo.sequent=$AGATHA -Dkey.fx.demo.autoprove.live=1 ;;
    treefilters)         run_flag treefilters 420 -Dkey.fx.verify.treefilters=1 -Dkey.fx.demo.sequent=$AGATHA -Dkey.fx.demo.autoprove.live=1 ;;
    tacletmatch)         run_flag tacletmatch 300 -Dkey.fx.verify.tacletmatch=1 -Dkey.fx.demo.sequent=$AGATHA ;;
    inputfreeze)         run_flag inputfreeze 360 -Dkey.fx.verify.inputfreeze=1 -Dkey.fx.demo.sequent=$AGATHA -Dkey.fx.demo.autoprove=1 ;;
    updatehighlight)     run_flag updatehighlight 300 -Dkey.fx.verify.updatehighlight=1 -Dkey.fx.demo.sequent=$USEQ ;;
    lemmaorigin)         run_flag lemmaorigin 300 -Dkey.fx.verify.lemmaorigin=1 -Dkey.fx.demo.sequent=$STRASSEN ;;
    joinmerge)           run_flag joinmerge 300 -Dkey.fx.verify.joinmerge=1 -Dkey.fx.demo.sequent=$AGATHA ;;
    joinmerge-gcd)       run_flag joinmerge-gcd 300 -Dkey.fx.verify.joinmerge=1 -Dkey.fx.verify.joinmerge.maxsteps= -Dkey.fx.demo.sequent=$GCD ;;
    proofmgmt-all)       run_flag proofmgmt-all 400 -Dkey.fx.verify.proofmgmt=all -Dkey.fx.demo.sequent=$AGATHA ;;
    extensions)          run_flag extensions 420 -Dkey.fx.verify.extensions=1 -Dkey.fx.demo.sequent=$AGATHA ;;
    exploration)         run_flag exploration 420 -Dkey.fx.verify.exploration=1 -Dkey.fx.demo.sequent=$AGATHA ;;
    caching)             run_flag caching 420 -Dkey.fx.verify.caching=1 -Dkey.fx.demo.sequent=$AGATHA ;;
    prooftree)           run_flag prooftree 420 -Dkey.fx.verify.prooftree=1 -Dkey.fx.demo.sequent=$AGATHA -Dkey.fx.demo.autoprove=1 ;;
    slicing)             run_flag slicing 420 -Dkey.fx.verify.slicing=1 -Dkey.fx.demo.sequent=$AGATHA ;;
    testgen)             run_flag testgen 420 -Dkey.fx.verify.testgen=1 -Dkey.fx.demo.sequent=$AGATHA ;;
    heatmap)             run_flag heatmap 420 -Dkey.fx.verify.heatmap=1 -Dkey.fx.demo.sequent=$STRASSEN ;;
    isabelle)            run_flag isabelle 300 -Dkey.fx.verify.isabelle=1 -Dkey.fx.demo.sequent=$NORM ;;
    sourceconsistency)   run_flag sourceconsistency 300 -Dkey.fx.verify.sourceconsistency=1 ;;
    autosave)            run_flag autosave 420 -Dkey.fx.verify.autosave=1 -Dkey.fx.demo.sequent=$AGATHA ;;
    minimizeinteraction) run_flag minimizeinteraction 420 -Dkey.fx.verify.minimizeinteraction=1 -Dkey.fx.demo.sequent=$AGATHA ;;
    # themepersist: the restore leg reads the preference persisted by the save leg, so the
    # two runs must stay inside one invocation
    themepersist)
      run_flag themepersist-s 300 -Dkey.fx.verify.themepersist=save -Dkey.fx.demo.sequent=$AGATHA
      run_flag themepersist-r 300 -Dkey.fx.verify.themepersist=restore -Dkey.fx.demo.sequent=$AGATHA
      ;;
    # modal-dialog flag (needs key dismissal via XTEST/xdotool)
    profileloadingdialog)
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
      ;;
    # SMT with real z3 from keyproject/setup-smt; apply/undo round trip
    smt) run_flag smt 900 -Dkey.fx.verify.smt=1 -Dkey.fx.demo.sequent=$AGATHA ;;
    # loadingexit: app must terminate ITSELF with exit code 0 (no pkill allowed)
    loadingexit)
      pkill -f '[d]e.uka.ilkd.key.core.fx.MainEx' 2>/dev/null; sleep 2
      export JAVA_TOOL_OPTIONS="-Xmx6g -Dprism.order=sw -Djava.io.tmpdir=$OUT/tmp -Dkey.fx.verify.loadingexit=1"
      ./gradlew --no-daemon --max-workers=1 :key.ui.fx:run > "$OUT/loadingexit.log" 2>&1 &
      GPID=$!; wait "$GPID"; rc=$?
      echo "loadingexit exit-code=$rc" >> "$OUT/RESULTS.md"
      if [ "$rc" -ne 0 ]; then echo "loadingexit" >> "$OUT/failed-flags.txt"; fi
      ;;
    proofdiff)           run_flag proofdiff 300 -Dkey.fx.verify.proofdiff=1 -Dkey.fx.demo.sequent=$AGATHA ;;
    drawer)              run_flag drawer 300 -Dkey.fx.verify.drawer=1 -Dkey.fx.demo.sequent=$AGATHA ;;
    drawerlayout)        run_flag drawerlayout 300 -Dkey.fx.verify.drawerlayout=1 -Dkey.fx.demo.sequent=$AGATHA ;;
    rightclickmacro)     run_flag rightclickmacro 300 -Dkey.fx.verify.rightclickmacro=1 -Dkey.fx.demo.sequent=$AGATHA ;;
    *) echo "unknown flag: $1 (known: ${ALL_FLAGS[*]})" >&2; return 1 ;;
  esac
}

finish() {
  local f
  for f in "$@"; do
    # themepersist runs under two log names (save/restore, see flag_recipe)
    if [ "$f" = themepersist ]; then
      summarize themepersist-s
      summarize themepersist-r
    else
      summarize "$f"
    fi
  done
  echo "SWEEP COMPLETE (flags: $*)" >> "$OUT/RESULTS.md"
}

# --- main --------------------------------------------------------------------------
: > "$OUT/failed-flags.txt"
start_display
if [ $# -eq 0 ]; then
  RUN=( "${ALL_FLAGS[@]}" )
else
  RUN=( "$@" )
fi
RAN=()
for f in "${RUN[@]}"; do
  echo "== $f" >> "$OUT/RESULTS.md"
  flag_recipe "$f"
  RAN+=( "$f" )
done
finish "${RAN[@]}"
if [ -s "$OUT/failed-flags.txt" ]; then
  echo "::error::UI verify sweep failed flags: $(paste -sd, "$OUT/failed-flags.txt")"
  exit 1
fi
echo "UI verify sweep: all flags PASS (flags: ${RAN[*]})"

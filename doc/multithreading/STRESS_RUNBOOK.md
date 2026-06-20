# Multi-core prover — 128-core stress runbook (one shot)

Goal: maximise the chance of surfacing a race/hang on a 128-core box, and capture enough on any
failure to trace it down afterwards. Run the phases in order; **phase 1 (`MtStressMatrix`) is the
main event** — the others are complementary. All are gated and do nothing in normal CI.

Branch: `bubel/mt-stress-perf` — the combined branch (`bubel/mt-perf-integration` = MT + the perf
series) plus this stress harness. It runs on the **compiled, cursor-free find-matcher by default**
(the perf series), which sidesteps the `PoolSyntaxElementCursor` lock that dominated run #1's
contention. To reproduce the legacy cursor-based matcher instead, pass `-Dkey.matcher.interpreter=true`
(it is forwarded to the per-proof children). Assertions are ON for all `key.core` test tasks (`-ea`),
which is important — let them catch invariant violations.

> **What run #1 taught us.** The first 128-core run was *GC-bound*: ~70% of wall time in GC pauses,
> 42k G1 evacuation failures, and a steadily growing ~17 GB live set across the hundreds of in-JVM
> runs — i.e. memory accumulated across proofs and turned the cursor-lock contention into a
> full-GC death-spiral that the watchdog reported as a HANG. So the harness now **forks one JVM per
> proof** (below): each proof starts from a clean heap, and a wedged proof is killed without taking
> the rest of the battery down.

## 0. Pre-flight
```bash
cd <repo>/key
ulimit -u            # max user processes/threads: should be >> 256 (workers are threads)
nproc                # confirm core count
./gradlew :key.core:compileTestJava   # warm the build once
```
Pick a heap that fits the box (the big proofs at 128+ workers want room): pass `-PstressHeap=<size>`
to the stress task, e.g. `-PstressHeap=64g`. Add `-Dkey.mt.jfr=<file.jfr>` to ANY run to attach a
Flight Recording (the build wires `-XX:StartFlightRecording` automatically).

## 1. Stress matrix — the main diagnostic battery (`MtStressMatrix`)
Corpus × worker-counts × reps. **Each proof runs in its own forked JVM** (clean heap per proof, and a
wedged proof is killed without aborting the battery). Each multi-core run is compared to a
single-threaded reference and classified OK / DIVERGE(sound but non-deterministic) / NONCLOSURE /
UNSOUND_CLOSE / EXCEPTION / HANG. Output: `key.core/build/mt-stress/`.

```bash
./gradlew :key.core:testMtStressMatrix -PstressHeap=4g \
    -Dkey.mt.stresstest.workers='1,2,4,8,16,32,64,96,128,192,256' \
    -Dkey.mt.stresstest.reps=30 \
    -Dkey.mt.stresstest.childheap=48g \
    -Dkey.mt.stresstest.proctimeout=5400 \
    -Dkey.mt.stresstest.jfrdir=$PWD/key.core/build/mt-stress/jfr \
    2>&1 | tee key.core/build/mt-stress/console.log
```
- The orchestrator JVM does no proving, so `-PstressHeap` stays small; **`-Dkey.mt.stresstest.childheap`
  sets the `-Xmx` of each per-proof child** — give *that* the big number (e.g. `48g`).
- `-Dkey.mt.stresstest.jfrdir=<dir>` records a **separate `<proof>.jfr` per child** (cleaner than one
  rolling file; correlate with that proof's `summary-<tag>.txt`). Omit it to skip JFR.
- `-Dkey.mt.stresstest.proctimeout=<sec>` (default 7200) force-kills a child whose JVM wedges →
  recorded as `PROCESS-HANG`; the battery continues.
- Worker counts deliberately go past 128 (192, 256) — over-subscription maximises interleaving.
- `reps=30` is a starting point; raise it if you have time budget (races are rare → more reps help).
- Default corpus is diverse + saturating (two wide synthetic problems + symmArray, ArrayList_concatenate,
  SLL.remove, Saddleback, observer, median, project). Override with `-Dkey.mt.stresstest.proofs=...`
  (comma list of example-relative `.key` paths and/or `synthetic:split_ifs:<n>` /
  `synthetic:split_work:<n>:<work>`). For pure saturation, e.g. `synthetic:split_ifs:15` = 32768 leaves.
- Per-run hang timeout: `-Dkey.mt.stresstest.timeout=900` (seconds).
- `-Dkey.mt.stresstest.fork=false` runs everything in one JVM (the old behaviour) — handy for a quick
  local smoke check, but loses the per-proof memory isolation.

**Collect afterwards (the whole directory):**
```
key.core/build/mt-stress/runs.csv          # aggregated: one row per run across all proofs
key.core/build/mt-stress/summary.txt       # aggregated: per-(proof,workers) tallies + anomaly list
key.core/build/mt-stress/runs-<tag>.csv    # per-proof rows (one file per forked child)
key.core/build/mt-stress/summary-<tag>.txt # per-proof tally
key.core/build/mt-stress/fail_*.txt        # ONE per anomaly: stacks, open-goal details, thread dump
key.core/build/mt-stress/console.log
key.core/build/mt-stress/jfr/<tag>.jfr     # per-proof Flight Recordings (if -jfrdir was set)
```

## 2. Wide-saturation timing/scaling (`MtSyntheticBenchmark`)
Generates wide proof shapes and times single vs N workers — confirms scaling up to 128 and exposes
allocation/GC behaviour at scale.
```bash
./gradlew :key.core:test --tests '*MtSyntheticBenchmark' -PstressHeap=64g \
    -Dkey.mt.benchmark=true -Dkey.mt.benchmark.threads='1,8,32,64,128,256' \
    -Dkey.mt.synth.splits=15 -Dkey.mt.synth.worksplits=9 -Dkey.mt.synth.work=200 \
    -Dkey.mt.jfr=$PWD/key.core/build/synth.jfr 2>&1 | tee key.core/build/synth.log
```

## 3. Existing over-subscribed stress gate (`testMtStress`)
The committed gate (symmArray ×reps, SLL, the macro path, the script + save/reload path) at a forced
8 workers — bump it way up for the big box. Each class runs in its own JVM (`forkEvery=1`).
```bash
./gradlew :key.core:testMtStress -PstressHeap=32g -Dkey.prover.parallel.threads=128 \
    2>&1 | tee key.core/build/mtstress-gate.log
```

## 4. Soundness equivalence gate (single vs multi, fingerprint-compared)
```bash
./gradlew :key.core:test --tests '*RealProofMtEquivalenceTest' --tests '*ProofEquivalenceTest' \
    -Dkey.prover.parallel.threads=128 2>&1 | tee key.core/build/equiv.log
```

## 5. Targeted JFR probe (only if a specific proof misbehaved in phase 1)
Runs ONLY the parallel prover on one proof, many reps, clean recording — for deep analysis of the
offender.
```bash
./gradlew :key.core:test --tests '*MtJfrProbe' \
    -Dkey.mt.jfr.probe=true -Dkey.mt.jfr.proof=<example-relative .key> \
    -Dkey.mt.jfr.workers=128 -Dkey.mt.jfr.reps=20 \
    -Dkey.mt.jfr=$PWD/key.core/build/probe.jfr 2>&1 | tee key.core/build/probe.log
```

## Reading the results
- **Only NONCLOSURE / UNSOUND_CLOSE / EXCEPTION / HANG are real failures.** DIVERGE = sound but a
  structurally different proof (expected for wide proofs; the parallel prover is order-dependent).
- **NONCLOSURE** `fail_*.txt`: look at the "open goals (serialNr : hasApplicableRule)" block. A goal
  that is open **and** `hasApplicableRule=true` was *abandoned* — the lost-goal race. The serial
  numbers point at the offending subtree.
- **EXCEPTION**: the captured stack is the concurrent-state offender (historically an
  `IndexOutOfBoundsException` from a shared mutable cache in matching).
- **HANG**: the thread dump shows every worker's stack — look for workers blocked on the scheduler
  monitor (lost wake-up) or a lock cycle (deadlock).
- Cross-reference timestamps in `console.log` / `runs.csv` with the `.jfr` (open in JDK Mission
  Control or `jfr print`) to see thread states / contention / allocation at the moment of a failure.

## If you only get one shot
Run phase 1 with the widest worker list and the highest `reps` your time budget allows, JFR on. It
already covers soundness (vs the single-core reference), non-closure, exceptions and hangs with full
diagnostics. Phases 2–5 are bonus signal if time remains.

# Multi-core prover — 128-core stress runbook (one shot)

Goal: maximise the chance of surfacing a race/hang on a 128-core box, and capture enough on any
failure to trace it down afterwards. Run the phases in order; **phase 1 (`MtStressMatrix`) is the
main event** — the others are complementary. All are gated and do nothing in normal CI.

Branch: `bubel/mt-goals` (or `bubel/mt-perf-integration` for the combined branch). Assertions are ON
for all `key.core` test tasks (`-ea`), which is important — let them catch invariant violations.

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
Corpus × worker-counts × reps. Each multi-core run is compared to a single-threaded reference and
classified OK / DIVERGE(sound but non-deterministic) / NONCLOSURE / UNSOUND_CLOSE / EXCEPTION / HANG.
Runs to completion (a hang aborts, after dumping all threads). Output: `key.core/build/mt-stress/`.

```bash
./gradlew :key.core:testMtStressMatrix -PstressHeap=64g \
    -Dkey.mt.stresstest.workers='1,2,4,8,16,32,64,96,128,192,256' \
    -Dkey.mt.stresstest.reps=30 \
    -Dkey.mt.jfr=$PWD/key.core/build/mt-stress/matrix.jfr \
    2>&1 | tee key.core/build/mt-stress/console.log
```
- Worker counts deliberately go past 128 (192, 256) — over-subscription maximises interleaving.
- `reps=30` is a starting point; raise it if you have time budget (races are rare → more reps help).
- Default corpus is diverse + saturating (two wide synthetic problems + symmArray, ArrayList_concatenate,
  SLL.remove, Saddleback, observer, median, project). Override with `-Dkey.mt.stresstest.proofs=...`
  (comma list of example-relative `.key` paths and/or `synthetic:split_ifs:<n>` /
  `synthetic:split_work:<n>:<work>`). For pure saturation, e.g. `synthetic:split_ifs:15` = 32768 leaves.
- Per-run hang timeout: `-Dkey.mt.stresstest.timeout=900` (seconds).

**Collect afterwards (the whole directory):**
```
key.core/build/mt-stress/runs.csv      # one row per run (status, closed, nodes, digest, time, ...)
key.core/build/mt-stress/summary.txt   # per-(proof,workers) tallies + anomaly list
key.core/build/mt-stress/fail_*.txt    # ONE per anomaly: stacks, open-goal details, thread dump
key.core/build/mt-stress/console.log
key.core/build/mt-stress/matrix.jfr
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

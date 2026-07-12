# Multi-core determinism probe

A small developer tool that finds **where a proof comes out differently** when KeY proves it on
several threads instead of one. You point it at a `.key` file; it proves that file once on a single
thread and many times on the multi-core prover, and tells you the first place the two disagree.

## What problem this is for

KeY can run its automatic proof search on several *worker threads* at once (the "multi-core
prover"): each worker takes one open goal and works on it while the others work on theirs. That is
faster, but it is only correct if the workers never disturb each other. If two workers accidentally
share and overwrite the same piece of memory, the proof search can take a different path on
different runs — sometimes it even fails to close a proof that the single-thread prover closes
every time. Such a bug is a **determinism bug**: same input, different result.

These bugs are hard to catch because they are rare and timing-dependent — a proof may go wrong only
once in a few thousand runs, and only when the machine is busy. This tool exists to catch them and,
more importantly, to say *where* the two runs first parted ways, so the cause can be found.

## The idea in one sentence

> A divergence is *the same decision producing a different answer in two runs.*

So the tool records, during proving, a stream of `(place, key, value)` entries — where `value` is
something that should always be the same for a given `key` — and then compares the single-thread run
against each multi-thread run. Wherever a `key` has two different `value`s, that is a divergence.

Each "place" is called a **site**. There are two kinds:

* a **comparison site** records a `(key, value)` in every run; the tool diffs the runs to find the
  keys where the value differs. Example: `proof-tree` records, for every node of the finished
  proof, which rule was applied there.
* an **invariant site** watches one of the prover's own internal consistency checks and reports
  when it trips *within a single run* — no second run needed, because a tripped check already proves
  the search was not deterministic. Example: `choice-point` watches the check the prover uses while
  it tries out rule instantiations.

## How it plugs in without changing KeY

The prover's source is **not** modified. The internal sites are added at start-up by a *Java agent*.
A Java agent is a small program the JVM loads before your `main` method; it is allowed to rewrite
the bytecode of classes as they load. Our agent inlines a few lines into the exact methods it wants
to watch, and those lines report to the tool. Because the code is inlined into the target class, it
can read that class's private fields directly. You switch sites on with a command-line option; you
never touch or rebuild KeY.

## Requirements

* **JDK 21** (the same Java the prover and CI use — the timing that triggers these races is sensitive
  to the Java version).
* This directory sits at `<keyRoot>/scripts/tools/mt`; its build pulls in the KeY modules from the
  same checkout automatically (a Gradle *composite build*), so there is nothing else to set up.

## Running it

From this directory:

```bash
./gradlew probe -Pproof=/path/to/Some.key
```

Useful options:

```bash
# turn on more sites (default is just choice-point; proof-tree is always on)
./gradlew probe -Pproof=/path/to/Some.key -Psites=choice-point,rule-cost

# more workers and repetitions -> more chances to hit a rare race
./gradlew probe -Pproof=/path/to/Some.key -Pworkers=4,8,12 -Preps=1500
```

The race is rare and timing-dependent, so **run it on a busy multi-core machine**. An easy way to
create load: in another terminal run one CPU-burner per core and stop them afterwards:

```bash
for i in $(seq 1 "$(nproc)"); do yes > /dev/null & done   # start load
# ... run the probe ...
kill %1 2>/dev/null; pkill yes                             # stop load
```

### Running it by hand (outside Gradle)

The build makes one self-contained jar that is *both* the agent and the driver library:

```bash
java -javaagent:build/libs/mt-divergence-probe.jar=sites=choice-point -ea \
     -cp "build/libs/mt-divergence-probe.jar:<key.core classpath>" \
     de.uka.ilkd.key.mtprobe.driver.DivergenceDriver Some.key workers=4,8 reps=1500
```

(The Gradle `probe` task assembles the classpath for you; the hand form is only needed to run the
agent against a completely separate KeY build.)

## Reading the output

```
mt-probe: proof=Some.key workers=[4, 8] reps/worker=1500 sites=[proof-tree, choice-point, rule-cost]
baseline: fullyClosed=true proof-tree keys=816 violations=0 warnings=29 (warnings are latent risks, not bugs)
run '8w#137':
  invariant violations (bugs): 1
    [choice-point] at position 1 the feature evaluation reached ...OneOfCP$... where a previous
      evaluation had ... -- non-deterministic feature evaluation
  warnings (latent risks, also in single-core): 29
  differs from the single-core baseline at 0 comparison key(s)
SUMMARY: 0 runs diverged from the single-core proof, 1 runs tripped a determinism check
```

Three things to read:

* an **invariant violation (bug)** names the site that tripped and the detail (for `choice-point`,
  which choice point differed and where) — the exact non-deterministic decision to investigate.
* a **comparison difference** names the site, the `key` (for `proof-tree`, the position in the tree),
  and the two values (which rule each run applied there) — the first node where the two proofs part.
* a **warning** is a *latent risk*, not a bug. The `rule-cost` site produces these, and — this is the
  point — the **single-core baseline has them too** (29 in the example). They mark places that
  *could* become order-dependent, useful when auditing, but they are normal and abundant, so they are
  counted separately and never make a run "fail".

`SUMMARY: 0 / 0` means no *bug* (violation) and no *tree divergence* in this run — warnings are
ignored for the verdict. For a *rare* race even `0 / 0` is not a clean bill of health: raise
`-Preps`, add load, or use more machines; absence over few runs is weak evidence.

## The sites that ship

| Site | Kind | What it measures |
|---|---|---|
| `proof-tree` | comparison (always on) | the finished proof: each node keyed by its position (branches sorted into a canonical order so a legitimate reordering of independent branches does not count), value = the rule applied there |
| `choice-point` | invariant | the prover's own check that a feature term evaluates the same way each time while it enumerates rule instantiations (a shared mutable field on a strategy feature breaks this) |
| `rule-cost` | invariant (warning) | when the rule-ordering comparison calls two *different* applicable rules "equal", so their order is left to timing — a latent risk, not proof of an actual divergence |

## Adding your own site

A site is small. To add one:

1. Pick the method to watch and write an **advice** class next to the others in `.../mtprobe/agent`.
   For a comparison site call `ProbeSink.observe("my-site", key, value)`; for an invariant site call
   `ProbeSink.invariantViolated("my-site", detail)`. Read whatever you need from the target with
   ByteBuddy's `@Advice.FieldValue`, `@Advice.Argument`, `@Advice.Return`, `@Advice.This`.
2. Register it in `DivProbeAgent.premain`: `if (ProbeSink.isEnabled("my-site")) { ... transform the
   target class ... }`.
3. Run with `-Psites=my-site`.

The one rule that matters: **choose a `key` that names the same logical decision in both runs.** The
multi-core prover records its events in a timing-dependent order, so you cannot line the runs up by
when things happened — only by a stable key (a branch path plus a position, say). Get the key right
and the two runs line up even though the multi-core run reordered everything; get it wrong and
everything looks different. That is why `proof-tree` keys nodes by a *canonical* position rather than
by the order the workers happened to build them.

## Note

This is a diagnostic tool, not part of the prover. It was written to find, and then confirm the fix
of, an intermittent determinism failure in the nonlinear-arithmetic proof `divisionAssoc.key`
(a strategy feature, `OneOfCP`, kept its chosen branch in a field shared by all worker threads).

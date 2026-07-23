# Writing prover code that works with the multi-core prover

KeY can run the automatic proof search on several *worker threads* at once (the
"multi-core prover", see `impl/ParallelProver.java`). Each worker picks an open goal,
works on it alone, and hands the finished rule application back. That has one big
consequence for everyone who writes prover code:

> **Any object that is not owned by a single goal can be used by several threads at
> the same time.** Taclets, strategy features, rule instances, indices and caches are
> all shared. If such an object *stores* something between two calls, two workers can
> write to it at the same moment and corrupt it.

You do not need to know much about multithreading to write safe code. Follow the four
rules below; each names the situation, the danger, and the pattern to use instead.
Worked, concrete examples (with the actual bugs they prevent) are in the KeY
documentation book under *Developer topics → Thread safety and determinism*.

## Rule 1: no plain mutable static fields on the proving path

A `static` field exists once for the whole program, so every worker sees the same one.
A plain `HashMap`, `ArrayList` or a non-`final` static counter in rule/strategy/proof
code will be read and written by several workers at once. `HashMap` is not built for
that: concurrent writes can lose entries or even make `get` loop forever.

The test `SharedStateLintTest` fails your build if you add such a field. Replace it,
depending on what you actually need:

| You need... | Use | Why this one |
|---|---|---|
| a cache where the value depends **only on the key** (same key ⇒ always same value, e.g. "the sort of this term") | `StripedLruCache` | Fastest under many threads. If an entry is evicted too early, the only cost is computing the same value again — the result never changes. |
| a cache where the value depends on **when it was first stored** (e.g. "the goal state at the time we first saw this rule app") | `ConcurrentLruCache` | Keeps one exact least-recently-used order for all entries. Slower (one lock for the whole cache), but eviction order can change results here, so it must be exact. |
| scratch memory that only helps the **current computation** (a "last input / last result" shortcut, a reusable buffer) | `ThreadLocal` | Every thread gets its own private copy, so nothing is shared at all. Use this for the common "remember the previous call" memo on a singleton. |
| a lookup table that is **filled once and then only read** | `final` field + immutable content (`ImmutableList`, `Map.copyOf`, `Collections.unmodifiableMap`) | Data that nobody writes can be read by any number of threads safely. |

How to decide between the two caches in one sentence: ask *"if this entry were thrown
away and computed again later, could the new value differ?"* If no → `StripedLruCache`;
if yes → `ConcurrentLruCache`.

## Rule 2: shared singletons must not remember anything between calls

Strategy features, rules and match instructions are usually single objects (`INSTANCE`)
used for *every* goal. Such an object must keep **no** mutable instance fields: all
per-call state belongs in parameters, local variables, or the per-goal objects that are
passed in. A "cache the last goal's result" field on a singleton is shared between
workers and produces wrong answers under the multi-core prover. If you really want that
shortcut, put it in a `ThreadLocal` (see Rule 1, third row).

## Rule 3: never let iteration order of an unordered collection influence proving

`HashMap` and `HashSet` return their elements in no guaranteed order. If that order
reaches rule selection (costs, candidate lists, queue order), the SAME proof can come
out differently on two runs — with any number of threads. Use collections with a fixed
order (`LinkedHashMap`, `LinkedHashSet`, `ImmutableList`) or sort before iterating.
The test `ScDeterminismTest` proves every corpus proof twice and fails if the two proof
trees differ, which is the typical symptom of this mistake.

## Rule 4: fresh names come from the goal, not from a global counter

New symbol names (`x_1`, `heapAfter_m`, ...) must be derived from the goal-local
namespaces, never from a counter shared by the whole proof. A global counter makes
names depend on which worker got there first, and reloading a saved proof then fails
because replay produces different names.

## Restricting a feature to the single-core prover

Sometimes making a feature thread-safe is not worth it (or not possible yet). That is a
legitimate choice — but it must be *declared*, so the feature runs single-core instead of
racing. Four mechanisms exist, from coarse to fine. Pick the coarsest one that fits.

**1. Profile level — don't opt in.** A whole profile (calculus + strategy) is kept off the
multi-core prover by simply not overriding `Profile.supportsParallelAutomode()`: the
default is `false`, and only `JavaProfile` opts in. Automode for a non-supporting profile
always runs single-core, whatever the user configured.

```java
// Profile.java (interface): conservative default, nothing to do for a new profile
default boolean supportsParallelAutomode() { return false; }
```

**2. Macro level — `allowParallel()`.** A proof macro whose strategy keeps cross-goal
state (a step counter over all goals, a stop-flag set by one goal for all others) declares
itself single-core by overriding one method; the macro machinery then routes it to the
single-threaded prover. Existing examples: `OneStepProofMacro` (counts steps across
goals), `AutoMacro`, `FinishSymbolicExecutionUntilMergePointMacro`.

```java
@Override
protected boolean allowParallel() {
    return false; // this macro's strategy shares state across goals
}
```

**3. Rule level — refuse applicability during a multi-core run.** A built-in rule that
cannot run concurrently (it touches other goals than its own) disables itself while a
multi-core run is active. Existing example: `MergeRule`, which links several goals and
would need to lock all of them:

```java
// MergeRule.isApplicable
if (ParallelProver.isMultiThreadedRunActive(goal.proof())) {
    return false; // merging links several goals; single-core only
}
```

The marker is scoped **per proof**: several proofs may be processed in parallel in one
JVM, and only the proof that the multi-worker run actually works on is marked. A proof
proved single-core at the same time — including a side proof spawned by a worker —
keeps its full rule set.

**4. Strategy level — keep the search from waiting for a disabled rule.** Mechanism 3
alone can stall a proof: if the strategy still *prefers* the disabled rule, goals wait for
a rule that never fires. Whoever disables a rule must also teach the strategy the
alternative. Existing example: with merge points set to "merge", the strategy treats them
as "skip" during a multi-core run (`SymExStrategy`, rule set `merge_point`), so proofs
pass merge points instead of stalling.

Use `ParallelProver.isMultiThreadedRunActive(proof)` (mechanisms 3 and 4) only as a last
resort: every such case distinction is a fork in behaviour that tests must cover twice.
Prefer the declarative switches (1 and 2). Side proofs need no action at all — they always
run single-core by design.

## Adding an exception to `SharedStateLintTest`

If the linter flags a field that is genuinely safe — for example a flag written only
before proving starts — allowlist it instead of restructuring:

1. Run `./gradlew :key.core:test --tests '*SharedStateLintTest*'`. The failure message
   names the field, e.g. `de.uka.ilkd.key.mypackage.MyClass#myTable`.
2. Open `key.core/src/test/resources/de/uka/ilkd/key/prover/mt/shared-state-allowlist.txt`
   and add one line: the field id, whitespace, and a justification that names *why no
   worker thread ever writes it during proof search*:

   ```
   de.uka.ilkd.key.mypackage.MyClass#myTable   # filled once in the static initializer, read-only afterwards
   ```
3. Re-run the test. It fails on stale entries too, so remove the line again if the field
   ever disappears.

An honest justification is the review contract: "it compiles" is not a reason, "written
only during single-threaded problem loading" is.

## When a multi-core CI test fails on your pull request

* `SharedStateLintTest` — you added a static mutable field on the proving path. The
  failure message names the field; fix it with the table above. If the field is truly
  safe (e.g. a setting written only before proving starts), add it to
  `shared-state-allowlist.txt` with a one-line justification.
* `ScDeterminismTest` — your change made proof search order-dependent (Rule 3 is the
  most common cause; a time-dependent cache, Rule 1 row 2, is the second).
* `RunSmallProofsMt2wTest` / `...4wTest` — a proof no longer closes (or got much
  bigger) under 2 or 4 workers, but works single-core. Typical causes: a shared object
  that remembers state (Rule 2), an unsafe cache (Rule 1), or global counters (Rule 4).
  Reproduce locally with `./gradlew :key.core:testMt2w`.

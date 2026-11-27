---
name: testing-taclet-java-semantics
description: Use when adding or changing a taclet that defines Java semantics (program rules in javaRules.key, integer/float semantics, loop or runtime-exception rules) and you must check that its \replacewith preserves the behaviour of its \find.
---

# Testing the Semantics of a Java-Semantics Taclet

## Overview

A Java-semantics taclet rewrites one Java program fragment (`\find`) into another
(`\replacewith`). Test it **without the prover**: write the matched fragment and the replaced
fragment as two *valid, standalone Java programs*, run each in its own JVM with `java`
(single-file source launch — no `javac`, no Gradle, no build), and compare their observable
results. Equal results over many instantiations is the evidence that the rewrite preserves Java
semantics.

## 1. Read the rewrite

```
ifElseUnfold {
    \find(\modality{#allmodal}{.. if(#nse) #s0 else #s1 ...}\endmodality (post))
    \varcond(\new(#boolv, boolean))
    \replacewith(\modality{#allmodal}{.. boolean #boolv; #boolv = #nse;
                                       if(#boolv) #s0 else{#s1} ...}\endmodality (post))
}
```

- `\find` → the **matched program**; `\replacewith` → the **replaced program**.
- `..` / `...` are context markers: the unchanged surrounding program. Put it in the shared
  wrapper, identical on both sides, so only the fragment differs.
- Schema variables (`#nse`, `#s0`, `#s1`) → concrete Java expressions and statements.
- `\varcond(\new(#boolv, boolean))` → a fresh, non-capturing local variable in the replaced
  program.
- `\assumes` / `{...#...}` guards → `if` guards or input choice, applied identically on both sides.
- Rule files: `javaRules.key` (program rules), `integer/intRules*Semantics.key`, `float/`,
  `loopRules.key`, `loopScopeRules.key`, `runtimeExceptions`, `heapRules.key`.

## 2. Complete the fragment into a valid program

A `\find`/`\replacewith` fragment is usually **not** a program: it carries `..`/`...` context
markers, free schema variables, and possibly an implicit `this` or a method frame. Complete it
minimally, and complete both sides **identically** so that only the fragment differs:

- **Class and entry point** — `public class Matched { public static void main(String[] args) { ... } }`;
  use an instance method when the fragment mentions `this`.
- **State** — declare and initialise everything the fragment reads (`int b = 0;`,
  `int[] a = {1, 2, 3};`, `boolean boolv = true;` for the name-clash case).
- **Context markers** — replace the leading `..` with the concrete statements your case needs and
  the trailing `...` with the statements that observe the state; keep both in the wrapper.
- **Method frame** — if the fragment only matches inside a method frame (`this[i] = v;` in the
  generated `$prepare()` body), model it as an instance method and call it.
- **KeYDL-only constructs** — `{#x := #e}` becomes `x = e;`; a `\new` variable becomes a local with
  a non-conflicting name; `\assumes`/`\varcond` become `if` guards or a dedicated case.
- **Checked exceptions** — declare the same `throws` clause on both sides.

If a fragment cannot be completed to valid Java by a mechanical translation, it relies on
prover-specific concepts; write the translation down in the case's comment.

## 3. Build the pair

One directory per instantiation, two self-contained programs that differ only in the fragment:

```
examples/ifElseUnfold/case-b0/Matched.java    (public class Matched)
examples/ifElseUnfold/case-b0/Replaced.java   (public class Replaced)
```

```java
public class Matched {                       public class Replaced {
    public static void main(String[] a) {        public static void main(String[] a) {
        int b = 0;                                   int b = 0;
        int x;                                       int x;
        if (b == 0) x = 1; else x = 2;               boolean boolv = (b == 0);
        System.out.println("x=" + x);                if (boolv) x = 1; else { x = 2; }
    }                                                System.out.println("x=" + x);
}                                                }
```

Print **everything observable**: return value, every variable the fragment can change, anything
printed. Keep the wrapper byte-identical on both sides (same inputs, same print statement).

## 4. Execute and compare

Use the JDK's single-file source launcher; no compilation step, a fresh JVM per program:

```bash
java Matched.java  > matched.out  2>&1; m=$?
java Replaced.java > replaced.out 2>&1; r=$?
[ "$m" = "$r" ] && diff -u matched.out replaced.out
```

A runnable driver for a whole example directory (`run.sh`) is next to the examples; it diffs the
stdout **and** the exit status of every pair.

## 5. Test many combinations

Enumerate the space the schema variables admit; every axis is a new matched/replaced pair:

| Axis | Examples |
|---|---|
| both branches | `b == 0` / `b != 0` |
| side effects | `if (i++ == 0) ...` — the condition must be evaluated exactly once |
| name clashes | a surrounding `boolean boolv;` — the `\new` variable must not capture |
| nesting | fragment inside an `if`, a loop, a method, a `try` |
| targets | locals, fields, arrays (`a[i] = ...`) |
| boundary values | `0`, `-1`, `Integer.MAX_VALUE`, `null`, empty arrays |

The example set in `examples/ifElseUnfold/` covers the branch, side-effect and name-clash axes.

## 6. Interpret a divergence

- **Different stdout/exit** → the `\replacewith` does not preserve the `\find`'s Java semantics for
  that instantiation: the taclet is wrong, or the example uses an instantiation the taclet does
  not allow.
- **A non-compiling program** (`java X.java` errors) → the example is wrong; fix it, never skip it.
- **A vacuous pair** (both print a constant; the fragment is not on the executed path) → enlarge
  the observable state until the fragment's effect is visible.
- Never adapt the wrapper or the printing to make a divergent pair agree.

## 7. Common mistakes

| Symptom | Cause |
|---|---|
| `java X.java` fails | the fragment was not completed into a valid standalone program (class, method, state, `..`/`...` context) — complete it identically on both sides |
| outputs equal but the test proves nothing | the fragment has no observable effect; assert its result and mutated state |
| divergence only in a stack trace or line number | compare the printed state, not the trace text |
| the pair differs outside the fragment | wrapper drift; regenerate `Replaced` from `Matched` |
| non-deterministic output | randomness, time or hash order; make the example deterministic |
| guards untested | `\varcond`/`\assumes` need their own instantiations (name clash, condition false) |

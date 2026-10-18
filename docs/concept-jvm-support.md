# KeY/JVM — Bytecode Verification by Transpilation to Java

**Concept & Implementation Plan** · branch `weigl/jvm` · status: draft v4 (ghost-`\seq` stack model; M1 proofs closing on `max`/`max2`)

---

## 1. Motivation and Goal

KeY verifies Java *source* programs. A large amount of relevant code exists only as bytecode:
compiled artifacts, library JARs, obfuscated or generated classes. This feature adds **JVM
support to KeY** without a second program logic or a new frontend. The trick:

> **Transpile bytecode back into Java source that KeY can already handle.** Every JVM
> instruction becomes a Java statement — `iload 5` becomes `stk.push(a);` with the operand
> stack formalized as the two ghost fields `\seq contents`/`int size` of the class `Local`,
> and the *behavior of the JVM* is specified by JML contracts on that class. Unstructured
> jumps are expressed as `jvm.Local.goto_(pc);` and handled by a small set of new built-in
> rules.

The transpiled output is **ordinary compilable Java** (`javac` must accept it), so the existing
machinery — JavaParser frontend, JML translation, method contracts, heap logic — is reused
unchanged. What is verified: a JML contract attached to the transpiled method holds; under the
trust assumptions of §8 this is a verification of the *bytecode* method.

## 2. Architecture Overview

Everything lives in **one new Gradle module `key.jvm`**; `key.core` is not touched. The
built-in rules are contributed by a **`JvmProfile extends JavaProfile`** (pattern: `WdProfile`
in `key.core.wd`), delivered through the standard `DefaultProfileResolver` service loader.

```
            ┌──────────────────────────────────────────────────────────┐
  .class ──►│  1. Transpiler (ASM-based, org.key_project.jvm.transpiler)│
  .jar  ───►│     bytecode → compilable Java + inlined JML + Local.java │
            └───────────────┬──────────────────────────────────────────┘
                            ▼
            ┌──────────────────────────────────────────────────────────┐
            │  2. JML formalization of the JVM (jvm/Local.java)        │
            │     typed stacks + typed locals, one contract per        │
            │     mnemonic; copied by the transpiler into every output │
            └───────────────┬──────────────────────────────────────────┘
                            ▼
            ┌──────────────────────────────────────────────────────────┐
            │  3. Goto rules (org.key_project.jvm.rule, same module)   │
            │     JvmProfile extends JavaProfile                       │
            │     GotoSpliceRule (forward) / GotoRestoreRule (backward)│
            └──────────────────────────────────────────────────────────┘
```

| Piece | Location |
|---|---|
| Transpiler + CLI | `key.jvm`, package `org.key_project.jvm.*` (deps: `org.ow2.asm` BSD-3-Clause, picocli) |
| JVM runtime `jvm.Local` + JML | resource in `key.jvm`, copied into each output folder |
| Rules + profile | `key.jvm`, package `org.key_project.jvm.rule`; `JvmProfile extends JavaProfile`, `JvmProfileResolver implements DefaultProfileResolver` |
| Wiring | `key.jvm/src/main/resources/META-INF/services/de.uka.ilkd.key.proof.init.DefaultProfileResolver` → `org.key_project.jvm.JvmProfileResolver` |
| Tests/fixtures | `key.jvm/src/test`, proofs via `KeYEnvironment.load` |

Profile selection: `ProofInitServiceUtil` resolves profiles by name from the service loader;
`JvmProfile` registers itself as `"java-jvm"` (`ident()`, `displayName()`, `description()`),
selectable like `"java-wd"` today. Rules are also resolvable by name from proof scripts
(`RuleCommand` reads `profile.getStandardRules().standardBuiltInRules()`).

```java
public class JvmProfile extends JavaProfile {
    public static final String PROFILE_ID = "java-jvm";
    public static final JvmProfile INSTANCE = new JvmProfile();
    @Override protected ImmutableList<BuiltInRule> initBuiltInRules() {
        // APPEND at the tail: UseOperationContractRule must stay FIRST (ProofMgt invariant)
        return super.initBuiltInRules()
                .append(GotoSpliceRule.INSTANCE)      // forward jumps, cost 0
                .append(GotoRestoreRule.INSTANCE)     // backward jumps, interactive
                .append(IfLiteralRule.INSTANCE);      // if(true)/if(false) unwrapping
    }
    // + ident()/displayName()/description() overrides, cf. WdProfile
}
```

## 3. Component 1 — The Transpiler

### 3.1 Pipeline

1. **Read** class files / JAR entries with ASM (`ClassReader`, `EXPAND_FRAMES`; add
   `org.ow2.asm:asm`, `asm-tree`, `asm-analysis` to `gradle/libs.versions.toml`).
2. **Analyze**: per method, CFG + verification types at every instruction (ASM `Analyzer` /
   `BasicVerifier`, cross-checked with `StackMapTable`).
3. **Structure (optional optimization)**: recognized javac shapes (if/else diamonds, simple
   loops) may be emitted as structured Java. **Correctness never depends on this** — the
   canonical emission is fully linear and every jump is a `goto_` call (§3.4).
4. **Emit**: class skeletons, fields, signatures (erased types are fine), method bodies,
   `jvm/Local.java`, stub classes for referenced-but-not-transpiled types, user JML inlined as
   `/*@ ... @*/` comments.
5. **Validate**: re-parse output; every `goto_` target label exists exactly once in the same
   method; last block ends in `return`/`throw`; compile with `javax.tools.JavaCompiler` —
   **transpilation fails loudly if the output does not compile**. Asserted by every test.

### 3.2 Transpilation principles

* **P1 — the operand stack is `Local` state; everything else is real Java.** JVM stack
  manipulation is a call on the frame's `Local` (`stk`): pushes/pops become
  `stk.push(v)` / `v = stk.pop()`, and neutral rearrangements/arithmetic are the mnemonic
  methods `stk.iadd()`, `stk.dup()`, `stk.swap()`, … (§4). JVM *local slots and parameters*
  are plain Java locals of the surrounding method — M1 needs no `Local`-side local model.
* **P2 — heap/object/compute ops become real Java.** KeY's heap logic and statement semantics
  are reused verbatim; `Local` only mediates the stack (M2+):
  * `getfield Foo.f` → `stk.pushRef(((Foo) stk.popRef()).f);`
  * `putfield Foo.f` → `{$1 = stk.popInt(); $2 = stk.popRef(); $2.f = $1;}`
  * `athrow` → `throw ((Throwable) stk.popRef());`
  * `invokevirtual/static/special` → pops into temps, real call, push result.
  Java's left-to-right evaluation order is made explicit with fresh temporaries (`$1, $2, …`,
  assigned immediately before use), so stack effects are unambiguous.
* **P3 — jumps are `goto_` calls; labels are Java labels.** Canonical emission is linear
  blocks with Java labeled statements as jump targets; the goto rules implement the jump
  (§5). Structuring into `if/else`/`while` is an optimization that reduces rule applications,
  applied only where it is provably equivalent.
* **P4 — one statement per instruction, pc as comment** (`// pc 16: iload 5`) so proof nodes
  map 1:1 back to bytecode locations.
* **P5 — fail loudly, never silently.** Untranslatable instructions (`invokedynamic`, `jsr/ret`,
  exotic stack shapes) abort transpilation with a precise message.

### 3.3 Instruction mapping (excerpt)

M1 emits plain-Java locals for JVM local slots and parameters (the operands land directly in
the surrounding method), and one `jvm.Local` stack frame for the operand stack:

| Bytecode | Emission | Contract style |
|---|---|---|
| `iconst_1`, `bipush 5`, `sipush` | `stk.push(1);`, `stk.push(5);` | singletize + concat (top-first) |
| `aconst_null` | `stk.push((Object) null);` | push constant reference (M2a) |
| `iload 1` / `istore 2` | `stk.push(a);` / `a = stk.pop();` | local `int` ↔ stack top |
| `aload 1` / `astore 2` | `stk.push(o);` / `o = (Foo) stk.popRef();` | local reference ↔ typed cast off `popRef` (M2a; `LocalVariableTable` types the slot) |
| `iinc 3, 1` | `c += 1;` | plain local update |
| `iadd`, `isub`, `imul`, `ineg`, `dup`, `swap`, … | `stk.iadd();` … | one contract per mnemonic |
| `ifeq`, `if_icmplt`, … | `if (stk.if_icmplt()) { jvm.Local.goto_(pc); }` (branch-taken predicate) | pops operand(s), returns `boolean` |
| `goto L` | `jvm.Local.goto_(7);` | *no contract* — goto rules (§5), int pc target |
| `ireturn`, `areturn`, `return` | `return stk.top();` … / plain `return;` | pops top |
| `idiv`, `irem`, bitwise, shifts | `stk.idiv();` … | *contractless* stubs (unused by M1 fixtures; would body-expand) |
| `ldc` (int/String/float/class) | `stk.push(7);`, `stk.push("…")` | push constant |
| `new`+`dup`+`invokespecial <init>` | `Foo f = new Foo($1, $2);` + push (fused; pattern validated) | constructor contract applies (M2a) |
| `get/putfield` | real Java field access: `(T) popRef` receiver + `recv.f`, `recv.f = v` (M2a ✓) | — |
| `get/putstatic` | real Java static access: `stk.push(Counter.calls);` / `int $v0 = stk.pop(); Counter.calls = $v0;` (M2 ✓) | — |
| `anewarray`, `aastore`, `aaload`, … | `aastore`/`aaload` on object arrays, multidim | exceptions from Java semantics (M3 follow-up: real Java array ops around pops/pushes, same pattern as `int[]`) |
| `newarray`, `iaload`, `iastore`, `arraylength` | real `int[]` ops: `int[] $a = new int[stk.pop()]; stk.push($a);`, `int $i = stk.pop(); int[] $a = (int[]) stk.popRef(); stk.push($a[$i]);`, `$a[$i] = $v;`, `stk.push($a.length);` (M2 ✓; only `T_INT`, other atypes abort) | Java array semantics |
| `checkcast`, `instanceof` | real Java cast / `instanceof`: `T $o = (T) stk.popRef(); stk.push($o);` resp. `stk.push($o instanceof T ? 1 : 0);` (M2 ✓) | `ClassCastException` from Java semantics |
| `invokevirtual/special/interface` | pop receiver+args into temps, real call on the receiver, push result (M2a ✓) | callee contract applies |
| `invokedynamic`, `jsr`, `ret` | **unsupported → abort** (M4+: `makeConcatWithConstants`) | — |

`goto` is a reserved Java word → method name `goto_`. `return` as a mnemonic is spelled by the
surrounding Java `return` statement. Jumps target the **bytecode pc**; `goto_(7)` matches label
`L7` (§3.4, §5.2).

**M2a status (objects & calls, shipped on `weigl/jvm`):** typed reference locals
(`aload`/`astore`; the slot type comes from the `LocalVariableTable`, and slot 0 of instance
methods is the implicit `this`), `aconst_null`, `areturn`, `getfield`/`putfield` (real Java
field access on the receiver popped off the reference stack), the `new`+`dup`+`invokespecial
<init>` fusion (`Point $t2 = new Point($c1, $c0);` — args popped between `dup` and `<init>`
must be pure argument pushes, otherwise the transpiler aborts loudly), and
`invokevirtual`/`invokespecial`(non-init)/`invokeinterface` (receiver and arguments popped
into typed temps, the call emitted on the *receiver expression*, e.g. `stk.push($o3.sum());`),
plus `ifnull`/`ifnonnull`/`if_acmp*` on the reference predicates. Explicit constructors are
emitted on the class (the canonical trivial javac default ctor, 3 ops, is skipped so M1 output
stays byte-stable); the implicit `super()` call is dropped, and an explicit non-Object
`super(args)` aborts loudly (the frame prologue would precede it, violating "super first").
The emitted shape is asserted by
`TranspileTest#transpiledObjectCodeHasCanonicalLayoutAndCompiles` and round-tripped through
`javac --release 17`. Static fields are shipped too (`get/putstatic`, M2): the real
`Owner.field` is read/written around int pops / typed `popRef` casts, booleans are normalized
to 0/1, and `<clinit>` initializers are dropped — static fields start at their JVM defaults
(0 / null), which is exactly what the `initialisation: disableStaticInitialisation` choice of
every proof assumes (pinned by
`TranspileTest#transpiledStaticFieldAccessHasCanonicalShape` against `golden/Counter.java`).
`checkcast`/`instanceof` emit real Java casts / type tests with the JVM's int 0/1 result
(`golden/Caster.java` + `TranspileTest#transpiledCastAndInstanceofHaveCanonicalShape`; the
`classify` shape additionally exercises the constrained-goto mid-layout return wrapper).
`int[]` arrays are shipped too (`newarray`/`iaload`/`iastore`/`arraylength`, M2): real Java
`int[]` operations with typed `popRef` casts of the array reference (`golden/Arrays.java` +
`TranspileTest#transpiledIntArrayOpsHaveCanonicalShape`). Stub generation remains an M2
follow-up.

### 3.4 Control flow: linear blocks, Java labels, `goto_`

Canonical emission is a linear sequence of *basic blocks*; every block that is a jump target
is a **Java labeled statement** whose label mirrors the pc:

```java
L7: {                       // pc 7: jump target (KeY AST: LabeledStatement)
    stk.push(b);
}
```

and every jump — forward or backward — is emitted as `jvm.Local.goto_(7);` (label `L7`
derived from the constant int argument). The two goto rules implement the jump (§5);
the transpiler does not need to resolve directionality.

**Label protection.** KeY's `unusedLabel` taclet (`javaRules.key`) strips `#lb: #s`
*anywhere in the remaining program* when `FreeLabelFinder` finds no occurrence of the label
inside `#s` — it scans for any `Label` node, so our `goto_` int arguments are invisible to
it, and it would strip a pending target while a `goto_` still references it. Therefore every
label that is the target of at least one `goto_` is emitted with a **guard** as first body
statement:

```java
L7: {
    if (false) { break L7; }   // javac-legal (JLS 14.22 blessing); makes
    stk.push(b);               // \freeLabelIn(L7, body) true → unusedLabel inapplicable
}
```

Labels referenced only by real `break`s (loop labels) are protected naturally; labels without
remaining gotos (e.g., merge points of structured diamonds) are not emitted at all.

**Structured emission (optimization, not requirement).** Where the CFG matches a javac shape:

1. **If/else diamonds** → `if (stk.if_icmplt()) { … } else { … }`, gotos to the merge point
   dropped, merge label dropped. (Always safe: the if-split keeps both arms' content in the
   same statement sequence, so residual `goto_`s inside arms still splice.)
2. **Loops** → `L4: while (!stk.if_icmpge()) { … }` with the comparison lifted into the
   guard; body-end back edges implicit; `continue` to header emitted as Java `continue;`
   (native loop-scope machinery); loop exits as labeled `break L4;`; jumps *inside* the body
   stay `goto_`s. A loop is only structured if **all** its jumps classify cleanly — otherwise
   the method falls back to linear emission (a `goto_` crossing a structured loop boundary
   would be misinterpreted by the invariant machinery, so it must never be emitted).
3. **`switch`** → `if`-chain on `stk.popInt()` (M3; Java `switch` later).

### 3.5 Exceptions

Exception tables are reconstructed as nested `try/catch` (ranges nest for javac output):

```java
try {
    …protected instructions…
    jvm.Local.goto_(pc);                    // normal path skips handlers (spliced)
} catch (Throwable $e) {
    stk.$caught($e);            // contract: resets machine state, stack := [$e]
    jvm.Local.goto_(pc);                    // or structured dispatch
}
```

`athrow` is a real Java `throw` (P2). Handler entry resets the machine (JVM discards the
operand stack; handler enters with `stack = [exception]`). Non-nested/overlapping handler
ranges → pc-tracked fallback (`stk.setPc(pc)` + dispatch chain) — M3, spike S4. Modern
`finally` (inlined bytecode + catch-`Throwable` entries) needs no extra machinery;
`jsr`/`ret` is unsupported.

### 3.6 Compileability

* javac rejects statements after `return`/`throw`; since `goto_`/`label` guards are ordinary
  calls/statements, the linear layout itself never creates unreachable code — but a
  mid-layout `return`/`throw` does. Every `return`/`throw` that is not the last statement of
  the body is wrapped: `if (true) { return stk.top(); }` (JLS 14.22 blessing), unwrapped by
  `IfLiteralRule` (§5.3). A value-returning body additionally ends in a dummy `return 0;`
  that is only reachable through the `if (false) { break L; }` guards of the label blocks
  (javac reachability otherwise flags it); the dummy never executes semantically.
* The JVM verifier guarantees the final block ends in `return`/`athrow` (validated), so a
  value-returning body never "falls off the end".
* Temporaries `$1, $2, …`, `stk`, and parameter names (from `LocalVariableTable` if
  available) cannot collide; generated code is data, exempt from spotless/checker-framework.

### 3.7 Class-level constructs

`<init>` → real constructors; `<clinit>` → static initializer; `this` stored into slot 0 by
the prologue. Synthetic accessors, inner classes, enums, records, interfaces/default methods,
varargs: M3/M4 items, each explicitly rejected before that.

### 3.8 Specifications

* `jvm/Local.java` (with JML) is copied into every output folder — self-contained and
  javac-checkable.
* User contracts are provided as sidecar `.jml` files; the transpiler **inlines** them as JML
  comments before the matching methods (KeY extracts JML from source comments in the frontend
  pipeline). Names/signatures preserved 1:1, so specs written against the bytecode method apply
  unchanged (modulo erasure).
* Loop invariants: for structured loops the transpiler emits `loop_invariant true;` skeletons;
  for linear/unstructured loops, specs attach to the **target label** (KeY already extracts
  block contracts from `LabeledStatement` — `JMLSpecExtractor.extractBlockContracts`) — §5.4.

## 4. Component 2 — JML Formalization of the JVM (`jvm.Local`)

### 4.1 State model

The operand stack is **not** a heap data structure and **not** a Java array — it is two
*ghost fields* of the M1 `Local` class, i.e. plain first-order logic values:

```java
package jvm;

public class Local {
    //@ public instance ghost \seq contents;   // top-first: element 0 = top
    //@ public instance ghost int size;        // stack height; bounds \seq_sub end indices

    public Local() { }                         // contract below
    public void push(int v) { }                // contract below
    public int  pop()  { return 0; }           // contract below
    public int  top()  { return 0; }           // contract below
    public void iadd() { }                     // …one contract per mnemonic…
    public boolean if_icmplt() { return false; } // …
    public static void goto_(int pc) { }       // NO contract — owned by the goto rules
}
```

* **Top-first `\seq`.** `contents[0]` is the top of the stack, `contents[size-1]` the bottom.
  Every operation is then expressible *length-free*: NJML's `\javaSource` translator (the
  `JmlParser`/`Translator` of `key.core`) has **no `\seq_length`/`.length` form**, so the end
  index of `\seq_sub` is taken from the `size` ghost instead:
  `push`: `contents == \seq_concat(\seq(v), \old(contents))`, `size == \old(size) + 1`.
  `pop`/`if_icmplt`: `contents == \seq_sub(\old(contents), k, \old(size))`.
* **`(int)` casts on element reads.** NJML resolves `\seq_get(…)` to an *any*-sorted term
  (`any::seqGet`), and arithmetic/relational operators NPE on non-`int` operands
  (`TypeConverter.getPromotedType`). Every element use inside an arithmetic, unary or
  relational context is therefore cast: `(int)\seq_get(\old(contents), 0)`. Plain reads like
  `\result == \seq_get(contents, 0)` and `== 0`/`!= 0` forms survive uncast; the sequence
  theory then sees `cast<int>(seqGet(…))` and `seqGetAlphaCast`/`castDel` take over.
* **Locals and parameters are plain Java.** The transpiler does not model JVM local slots as
  `Local` state at all — `iload 1` becomes `stk.push(a);` on the surrounding method's real
  parameter/local `a`.
* **No heap, no objects, no NPEs.** Because the stack is a `\seq` ghost there are no heap
  fields to touch: a proof over a transpiled M1 method reasons about exactly one `Local`
  instance (created up front by `stk = new jvm.Local();`), its `\seq`-formulas, and the
  method's own int locals.
* **`goto_` is static and contractless** (int pc argument; label `L<pc>`): with no contract,
  `UseOperationContractRule` can never claim it — the goto rules own it exclusively (§5).

### 4.2 Contract patterns and the two rules they depend on

```java
/*@ public normal_behavior
  @   assignable contents, size;                      // NEW: constructor contract (see below)
  @   ensures contents == \seq_empty;
  @   ensures size == 0;
  @*/
public Local() { }

/*@ public normal_behavior
  @   assignable contents, size;
  @   ensures size == \old(size) + 1;
  @   ensures contents == \seq_concat(\seq(v), \old(contents));
  @*/
public void push(int v) { }

/*@ public normal_behavior
  @   assignable contents, size;
  @   requires size > 0;
  @   ensures \result == \seq_get(\old(contents), 0);
  @   ensures size == \old(size) - 1;
  @   ensures contents == \seq_sub(\old(contents), 1, \old(size));
  @*/
public int pop() { return 0; }

/*@ public normal_behavior
  @   assignable \nothing;                             // read-only (see below)
  @   requires size > 0;
  @   ensures \result == \seq_get(contents, 0);
  @*/
public int top() { return 0; }

/*@ public normal_behavior
  @   assignable contents, size;
  @   requires size >= 2;
  @   ensures \result ==
  @           ((int)\seq_get(\old(contents), 1) < (int)\seq_get(\old(contents), 0));
  @   ensures size == \old(size) - 2;
  @   ensures contents == \seq_sub(\old(contents), 2, \old(size));
  @*/
public boolean if_icmplt() { return false; }
```

Two hard-won rules of this model (both discovered by proof-experiments on the M1 fixture and
encoded in the runtime):

1. **The constructor must get a contract.** KeY's `allocateInstance`/`create` initializes a
   freshly created object's fields to their *defaults* — and the default of a `\seq`-typed
   ghost field is **`null`**, not the empty sequence. Every downstream contract formula
   (`\seq_concat(\seq(v), \old(contents))`, `\seq_sub`, …) would then fight a `null` sequence
   argument, and the sequence simplification rules (`getOfSeqSingleton`,
   `lenOfSeqConcat`, `elementOfSingleton`, …) never fire on malformed sequences — the proof
   simply stalls. The contract on `Local()` (with `methodExpansion: modularOnly`) replaces the
   `new jvm.Local()` call so callers see `contents == \seq_empty && size == 0`.
2. **Read-only operations must declare `assignable \nothing`.** The JML default for a method
   without an `assignable` clause is `\everything`: the created frame becomes `allLocs` and
   `UseOperationContractRule` models the post-state with an *unconstrained* fresh anon-heap
   function for the whole heap. A post-condition read like `\result == \seq_get(contents, 0)`
   then refers to a value that is provably unrelated to the stack — the goal is semantically
   unprovable. With `assignable \nothing` (read-only: `top`) or a precise frame
   (`contents, size`: everything that pops/pushes/rearranges), the at-pre heap of the callee
   equals the caller's heap on everything outside the frame, and the sequence facts flow.

Both are part of the runtime contract discipline: *every* operation declares a frame, and the
constructor restores the empty-sequence invariant that the JVM default initialization does
not.

Notes:

* **Math mode**: contracts use Java semantics (wrapping) — int arithmetic is Java-int
  arithmetic; proofs run with `intRules: javaSemantics` (set by the generated `.key` files).
  Caveat: auto-mode total-correctness proofs of `\measured_by` recursion and of fresh-object
  constructor residuals fall back to `arithmeticSemanticsIgnoringOF`, see §9.1.
* **No class invariant.** The ghost fields need no `\invariant_for(local)` beyond the trivial
  wellFormedness KeY adds automatically; the `size` ghost and the sequence are coupled only
  through the per-operation contracts (a full `size == \seq_length`-style invariant is
  impossible anyway — NJML has no length operator).
* **Contractless stubs** (`idiv`, `irem`, bitwise, shifts): unused by the M1 fixtures; if the
  strategy ever meets one it body-expands the empty Java body, so proofs must not rely on
  them. Division/remainder/bitwise semantics need JavaDL theory that M1 intentionally avoids.
* `$caught` (M3): exception handler entry resets the machine, `stack := [e]` —
  `assignable contents, size; ensures size == 1 && contents == \seq(e);`.
* Runtime self-verification (M4): prove `Local`'s implementation against its contracts,
  cross-checked against the JVM Specification.

## 5. Component 3 — The Goto Rules

### 5.1 Classification: forward vs. backward

During symbolic execution statements are **eaten up** from the front, so the remaining program
of a goal is a suffix of the method body. A jump target label is either

* **still present** in the remaining statement list of the *same method frame* → **forward
  jump**, or
* **gone** (already consumed) → **backward jump**.

JVM jumps are always method-local, so the search is scoped to the innermost `MethodFrame` of
the current `JavaBlock` — never across frames. This single test drives both rules.

### 5.2 `GotoSpliceRule` — forward jumps

Modeled on `SetStatementRule`. Applicability: top-level succedent, not inside a `Transformer`;
active statement (`JavaTools.getActiveStatement`) is a `MethodReference`
`jvm.Local.goto_(pc)` with a constant **int** argument whose label `L<pc>` is found in the
remaining statement list of the innermost method frame.

Application:
1. Take the innermost frame's statement list; build the new list
   `[before goto] ++ [label body without guard] ++ [after the labeled block]`
   — i.e. delete the range `[goto_ … labeled block)` and splice the target body in its place.
   Implemented as one pass: construct a fresh `StatementBlock` from the old statement list
   (nodes reused) and swap it via `JavaTools.replaceStatement`, or a small
   `CreatingASTVisitor` — same pattern as `JavaTools.replaceStatement`/`ProgramElementReplacer`.
2. Drop the leading guard `if (false) { break L; }` from the spliced body (shape-recognized;
   abort loudly if not recognized — transpiler controls the shape).
3. Rebuild `tb.prog(modality.kind(), JavaBlock.createJavaBlock(block), post, labels)` with the
   preserved `MethodFrame` (`JavaTools.getInnermostMethodFrame`), `goal.split(1)` +
   `changeFormula` — exactly like `SetStatementRule`.

Soundness: the deleted range is unreachable after an unconditional jump *in this goal*; every
branch's pending gotos live in their own goals (if-split etc. fork them). Cost 0 → applied
before anything else can reinterpret the jump. Loud abort (never silent fall-through) if the
label is missing at the same frame level.

### 5.3 `IfLiteralRule` — constant-condition wrappers

The reachability wrappers and the label guards produce literal-condition ifs that must not go
through `ifElseSplit`'s update-on-literal path. Applicability: active statement is an `If`
with literal `true`/`false` guard. Application: `if (true) { S }` → `S`;
`if (false) { break L; }` → `{}` (cleaned by the existing `blockEmpty` taclet). Cost 0.

### 5.4 `GotoRestoreRule` — backward jumps

The statements before the current position are gone from the remaining program, so a backward
target must be recovered **from the original method**:

Applicability: active statement is `jvm.Local.goto_(pc)` and the label `L<pc>` is **not**
found in the remaining statement list of the innermost method frame.

Application:
1. Find the current method frame: `JavaTools.getInnermostMethodFrame(javaBlock, services)`.
2. Get the original program: `frame.getExecutionContext().getMethodContext()` →
   `IProgramMethod` → `getBody()` — the untouched `StatementBlock` of the transpiled method,
   with all labels intact (proof rules never transform the *declared* body, so backward
   targets are always recoverable — this is why the mechanism is robust).
3. Locate the `LabeledStatement` with label `L` in that body (must exist; jumps are
   JVM-local; abort loudly otherwise).
4. Cut everything up to the target: the new statement list is the **suffix**
   `[L: {…} … end of original body]`.
5. Replace the remaining statement list *inside that method frame* with the suffix (frame and
   everything outside it preserved; accumulated updates in the update prefix stay — the state
   at the jump is the state entering the target). Re-embed with `tb.prog(…)`, `goal.split(1)`.

Semantics: this is **semantic loop unrolling** — each application executes one more iteration;
reaching the backward `goto_` again re-applies the rule. Sound per application. Consequences:

* **Not auto-mode friendly**: unbounded loops would be unrolled forever. The rule therefore
  gets no cost-0 treatment — it is applied interactively, or (Phase 3) only when a
  specification is attached to the target label. For javac-shaped loops the transpiler's
  structured emission (§3.4) avoids the situation entirely by producing real `while` loops
  with native JML `loop_invariant` handling.
* **Phase 3 — invariant-based application**: KeY already extracts block contracts from
  `LabeledStatement` (`JMLSpecExtractor.extractBlockContracts`); a JML spec on the target
  label can drive an invariant-style application of `GotoRestoreRule` (establish/preserve/use
  split à la `LoopInvariantRule`) instead of unrolling.
* Auto-mode gating mechanism (settings/choice vs. strategy cost) — spike S5.

### 5.5 Registration and justification

All three rules are registered by `JvmProfile.initBuiltInRules()` (appended after
`UseOperationContractRule`, which must stay first). Forward splice + literal unwrap: cost 0.
Backward restore: interactive/high cost. Soundness of the three program transformations is
small, well-scoped, and reviewable; a meta-lemma proof is future work. The rules abort loudly
(`RuleAbortException`) on any shape the transpiler would never produce.

## 6. End-to-End Examples

### 6.1 Branch — javac output of `int max(int a, int b) { return a >= b ? a : b; }`

M1 emission (golden fixture `golden/Max.java`; goto targets are the pc):

```java
int max(int a, int b) {
    jvm.Local stk = new jvm.Local();
    stk.push(a);                            // pc 0: iload_1
    stk.push(b);                            // pc 1: iload_2
    if (stk.if_icmplt()) { jvm.Local.goto_(7); }  // pc 2: if_icmplt 7 (true iff a < b)
    stk.push(a);                            // pc 5: iload_1
    jvm.Local.goto_(10);                    // pc 6: goto 10
    L7: { if (false) { break L7; }          // pc 7: label guard
        stk.push(b);                        // pc 10: iload_2
    }
    L10: { if (false) { break L10; }        // pc 10: label guard
        return stk.top();                   // pc 13: ireturn
    }
    return 0;                               // unreachable dummy (see §3.6)
}
```

Proof (closed automatically by the auto strategy): the `Local()` constructor contract
initializes the ghost stack to `\seq_empty`/`0`; `push` contracts put `[b,a]` on the stack
(top-first); `if_icmplt`'s contract splits on `a < b` (having popped both operands); the
taken branch splices once (`GotoSpliceRule`, guard dropped), the fall-through after the goto
is deleted; `top()`'s contract (read-only, frame `\nothing`) yields `\seq_get(\seq(v), 0)`
for `v = a` or `v = b`; `getOfSeqSingleton` gives `\result == a` resp. `\result == b` —
`\result == a >= b ? a : b` closes.

### 6.2 Loop — javac output of `int sum(int n) { int s = 0; for (int i = 0; i < n; i++) s += i; return s; }`

*Structured emission (Mode S, M1 design sketch — not yet implemented):*

```java
public int sum(int n) {
    jvm.Local stk = new jvm.Local();
    int s = 0, i = 0;                    // pc 0-3: iconst_0; istore 2/3
    stk.push(i); stk.push(n);            // pc 4-6: iload_3; iload_1
    L4: while (!stk.if_icmpge()) {       // pc 7: if_icmpge 19
        stk.push(s); stk.push(i);        // pc 9-10: iload_2; iload_3
        stk.iadd();  s = stk.pop();      // pc 11-12: iadd; istore 2
        i++;                             // pc 13: iinc 3, 1
        stk.push(i); stk.push(n);        // pc 16: goto 4 — implicit back edge
    }
    return s;                            // pc 19,20
}
```

with a native JML `loop_invariant` (e.g. over the plain-Java locals `s`/`i`).

*Linear emission (Mode L) of the same method* keeps pc 16 as a real backward jump:

```java
    L4: { if (false) { break L4; }
        stk.push(i); stk.push(n);
        if (stk.if_icmpge()) { jvm.Local.goto_(19); }
        stk.push(s); stk.push(i); stk.iadd(); s = stk.pop(); i++;
        jvm.Local.goto_(4);
    }
    L19: { if (false) { break L19; } return s; }
```

Execution applies `GotoSpliceRule` at pc 4 (fall-through entry: guard stripped by
`IfLiteralRule`), splices at the conditional exit, and applies `GotoRestoreRule` at the
backward `goto_(4)` — one unrolling step per iteration (interactive, or Phase-3 label
invariant).

### 6.3 Driving a proof

```kotlin
val env = KeYEnvironment.load(pathInProject("build/transpiled"), listOf(specsDir), null)
val proof = env.proveContractByName("Foo.sum(int).JML normal_behavior operation contract.0")
env.uiControl.startProof(proof)   // auto mode; assert closed
```

or a `.key` file with `\javaSource "build/transpiled";` + `\proofObligation { … }`, loaded
with profile `java-jvm`.

**Strategy selection (M1 lesson).** Programmatic proofs must be driven with the *real* auto
strategy — `de.uka.ilkd.key.macros.DefaultAutoMacro` (= the "Auto" button: `AutoProvers` →
`ApplyStrategy` on the proof's active strategy). Using `ScriptAwareMacro` instead
(symbolic-execution-only + try-close, designed for JML proof *scripts*) silently stalls as
soon as the program calls a method of a *second* user class (even a plain
`Helper h = new Helper()`): the symbex-only pass filters out the contract/expansion rules
for cross-class calls and the strategy gives up on the goal. All M1 proof gates therefore
run `DefaultAutoMacro` (strategy timeout bounds CI time).

## 7. Verification Workflow and Trust Assumptions

A closed proof of the transpiled method's contract establishes, modulo:

* **T1** ASM reads the class file correctly (mature).
* **T2** JVM verifier soundness: verification types used for the typed stacks are consistent
  along executions (documented meta-lemma; future in-system lemma).
* **T3** Transpiler faithfulness: instruction-by-instruction mapping argument (§3.2) +
  differential execution tests (transpiled vs. original bytecode, M3) + the
  output-compileability invariant.
* **T4** `Local` contracts faithfully encode JVMS: implementation-verification proofs (M4) +
  cross-check against the JVM Specification.
* **T5** The goto rules implement jump semantics (forward splice; backward restore from the
  original body) — small, reviewable transformations.

… the bytecode method satisfies the JML contract: verification of the compiled artifact.

## 8. Testing Strategy

| Level | What | Where |
|---|---|---|
| Unit | CFG/typing/structuring on synthetic `.class` fixtures | `key.jvm/src/test` |
| Golden | transpile → `javac` compiles output (hard invariant) | every transpile test |
| Differential | run transpiled vs. original bytecode on random inputs | M3 |
| Proof | `KeYEnvironment` + `.key` fixtures: max, max2 (M1, closed); recursion-by-contract (M1, closes under arithmetic int rules, see §9.1); sum (both modes), factorial, goto-heavy control flow, exceptions (M2/M3); object slice (M2, golden Point/Shapes: layout + javac round-trip, residual-shape pin per §9.1) | `key.jvm/src/test` |
| Rule | `GotoSpliceRule`/`GotoRestoreRule`/`IfLiteralRule` unit tests incl. negative cases (missing label → loud abort) | `key.jvm/src/test` |
| Regression | RunAllProofs proof collection once stable | `key.ui/examples` |

## 9. Milestones

| Milestone | Scope | Acceptance criteria | Est. |
|---|---|---|---|
| **M0** scaffolding | `key.jvm` module (settings.gradle, ASM deps), CLI skeleton, `JvmProfile` + resolver + services wiring (registered, selectable), `Local.java` draft (int-only) | `./gradlew :key.jvm:build` green; profile `java-jvm` appears in profile resolution; CLI transpiles a class | 2–3 d |
| **M1** int end-to-end | int subset (constants, iload/istore/iinc, iadd-family, branches, goto forward+backward, labels+guards, returns); all three rules; transpile→javac→prove pipeline; spec inlining; Mode S for simple loops | 3–5 proof tests closed (max, sum both modes, factorial); outputs compile | 1–2 wk |
| **M2** objects & calls | aload/astore, null, checkcast/instanceof, get/putfield/static, new+ctor fusion, invoke\*, int[] arrays, stub generation | linked-list/array example verified incl. method contracts | 2–4 wk |
| **M3** full control flow | try/catch/finally, switch, long/float/double, full stack shuffles, differential harness, pc-tracked fallback, label-spec invariant application (Phase 3 pull-forward if needed) | fixtures with exceptions, switches, longs prove; differential tests pass | 3–6 wk |
| **M4** integration & story | `.jml` merging polish, UI/CLI "Load bytecode/JAR", docs, RunAllProofs entries, `Local` implementation verified, performance pass | usable by non-authors; runtime contracts discharged | 2–4 wk |

M1 is the de-risking step; upstreamable PR (module + profile + rules) early.

**M1 status (on `weigl/jvm`):** the ghost-`\seq` runtime (§4) with the constructor contract
and per-operation frames is in place; `JvmProfile` wires `UseOperationContractRule` first and
appends the three goto rules; the transpiler emits the golden shape (asserted by
`TranspileTest`; `javac --release 17` accepts the output); **the `max` and `max2` contract
proofs close** (`GotoProofTest` under the auto strategy — the forward-goto `max` and the
mid-layout-return + goto `max2`). Blockers resolved: the `\seq` ghost defaulting to `null`,
read-only ops missing `assignable \nothing`, and the `ScriptAwareMacro` stall (§4.2, §6.3).
In flight: backward-jump/loop fixtures (Mode L + `GotoRestoreRule`), `sum`/`factorial`.

**Recursion (item 2) is shipped in two halves.** (a) The transpiler emits the recursive
self-call faithfully — the popped argument into a temp followed by a *real* call
`stk.push(fact($v0))`, see `MethodTranspiler.INVOKESTATIC` handling — and `TranspileTest`
round-trips `Fact.class` through javac (canonical shape asserted). (b) The *proof* side is
covered by `RecursionProofTest`: operation-contract recursion at a `\measured_by` closes in
auto mode under the `java-jvm` profile with `intRules: arithmeticSemanticsIgnoringOF` — the
same math mode KeY's own recursion reference (`key.ui/examples/standard_key/java_dl/recursion/`)
uses. Proving the *transpiled stack-model* `Fact` additionally needs the fresh-`jvm.Local`
createdness residuals that the default strategy leaves open in auto mode (see below).

**M2a status (on `weigl/jvm`):** the object-call slice of the transpiler is shipped and
fidelity-tested — reference ops on `jvm.Local`, slot typing from the `LocalVariableTable`
(implicit `this`), field access, `new`+init fusion and instance calls (§3.3), and static
fields (`get/putstatic`, `<clinit>` dropped), casts/type tests (`checkcast`/`instanceof`) and
`int[]` arrays (`newarray`/`iaload`/`iastore`/`arraylength`), checked by `TranspileTest`
(canonical shapes + `javac --release 17` round-trip) against the golden twins
`golden/Point.java` + `golden/Shapes.java` + `golden/Counter.java` + `golden/Caster.java` +
`golden/Arrays.java`. The *proof* side is blocked by the KeY-side fresh-object residual of
§9.1 (2): any Object-typed stack op leaves `created(pre, frame)` goals open in auto mode, so
the object fixtures are pinned as a characterization (`ObjectProofTest`) rather than as
closing gates. Next M2 slice: stub generation — followed by the §9.1 follow-ups that unlock
closing object proofs.

### 9.1 Known limitations (M1)

Two KeY-side strategy gaps bound what auto mode can close under the `java-jvm` profile. Both
are *strategy* limits, not rule bugs, and both are pinned by deterministic tests so that a
KeY-side improvement is noticed and converted deliberately.

1. **`intRules: javaSemantics` + `\measured_by` recursion.** A total-correctness (diamond)
   recursion PO does not close under `DefaultAutoMacro` with `intRules: javaSemantics`
   (`RecursionProofTest.measuredByRecursionUnderJavaSemanticsDoesNotCloseInAutoMode`); the same
   PO closes with `arithmeticSemanticsIgnoringOF`
   (`measuredByRecursionClosesUnderArithmeticIntRules`). This is independent of the stack
   model — even a pure-int recursive method reproduces it. KeY's own recursion examples use
   `arithmeticSemanticsIgnoringOF` for the same reason.
2. **Fresh-object residuals of the `jvm.Local` constructor contract.** Contracts applied to
   `new jvm.Local()` inherit a free post "the object is created (and non-null) in the
   post-state / was fresh in the pre-state". Closing that against the constructor's anon-heap
   needs the `selectCreatedOfAnon` reduction, whose heuristic band
   (`simplify_heap_high_costs`) the default strategy binds to infinity (`JavaCardDLStrategy`).
   The residuals can therefore surface as succedent goals of the shape
   `created(heap, self_0)`, `self_0 != null` (origin `ensures @ file Local.java`) in the
   initial pre-heap — semantically derivable, but beyond auto mode. `GotoProofTest`
   `factRecursiveContractGoalShape` pins the exact goal shape for the transpiled recursive
   `Fact`. Follow-ups: an interactive script in the vein of `triangular.proof` that applies
   the reduction once, or a KeY change making the high-cost heap simplifications available to
   auto mode.
   <p>
   **M2 finding — the discriminator is Object-typed stack traffic.** Experimental isolation
   (`probe` runs against minimal methods, varying one stack op at a time) shows that
   *int-only* flows — all of M1 — never materialize the residual, while *any* Object-typed
   operation (`push(Object)`, `popRef()`, `topRef()`) does, closing-independent of
   `intRules` (arithmetic semantics does not help: the goals are heap facts, not arithmetic,
   and M1's recursion workaround therefore does not carry over). Consequence: no object-slice
   method contract closes under `DefaultAutoMacro` today — including the M2 fixtures
   (`Point::sum`, `Shapes::total`, `Shapes::make`). `ObjectProofTest`
   (`objectSliceLeavesFreshObjectCreatednessResidualsOpenInAutoMode`) pins the residual goal
   shape against the golden `Shapes::make`. Replacing the constructor-contract initialization
   by a body-expanded allocation + an `initialize()` *method* contract was experimentally
   ruled out too: without the constructor contract's anon-post, even int-only flows stop
   closing (the strategy cannot push the `create`-update's createdness out of the pre-heap).
   The object proof story therefore waits on the same two follow-ups listed above.

Unrelated to the above, `JvmProfile` does *not* change the underlying strategy — the three
appended rules fire at cost 0; the `max`/`max2` gates close under the full M1 settings
(§4.2) including `intRules: javaSemantics`.

## 10. Risks, Open Questions, Spikes

* **S1 (M1)** Rule ordering: no contract exists for `goto_`, so `UseOperationContractRule`
  must not claim it; verify cost-0 behavior and that body-expansion taclets don't grab it.
  *(resolved on `weigl/jvm`: `goto_` is static+contractless, `GotoSpliceRule` fires at cost 0,
  both gates close).*
* **S2 (M2)** Forward splices *inside* structured loop bodies: confirm labels of the body are
  visible in the body-branch program (dump branch sequents). Mode L is unaffected.
* **S3 (M1)** Literal-condition ifs (`if (true) {…}` wrappers, `if (false) { break L; }`
  guards): check `ifElseSplit` behavior on literals; `IfLiteralRule` at cost 0 should win;
  fallback guard variant: `if (local.$$dead()) { break L; }` with `ensures \result == false`.
  *(resolved on `weigl/jvm`: `IfLiteralRule` handles both shapes; the `if (false)` guards are
  emitted for every goto target and are dropped together with the splice/restore).*
* **S4 (M3)** Jumps out of `try` regions and overlapping exception ranges (restore vs. break
  vs. pc-tracking).
* **S5 (M1/M2)** Auto-mode gating of `GotoRestoreRule` without touching `key.core`:
  strategy cost requires `SymExCost`/`StaticFeatureCollection` (core); module-local
  alternative: rule consults a setting/choice (`OneStepSimplifier` precedent) or spec presence.
* **R1** Proof size grows with instruction count (one contract application per instruction).
  Mitigations: structured emission, later Mode B (SSA lowering).
* **R2** A missed goto rule application would change semantics silently (fall-through).
  Mitigations: no-contract trick (stuck goal = visible), loud `RuleAbortException`,
  transpiler-side output validation, targeted tests.
* **R3** KeY float/double support less mature than int/long — floats late (M3).
* **R4** `invokedynamic` (lambdas, string concat in modern javac) — unsupported at first;
  targeted `makeConcatWithConstants` support in M4 or require `-XDstringConcat=inline` inputs.
* **R5** Library calls have no contracts → weak default frames; users spec used library
  methods (KeY's JavaRedux stubs cover parts of `java.lang`/`java.util`).
* **R6** ASM is BSD-3-Clause (compatible with GPL-2.0-or-later; record in third-party notices).

## 11. Alternatives Considered

| Alternative | Verdict |
|---|---|
| `local.label("…")` marker calls instead of Java labels | dropped per review: reuses no Java syntax, extra rule; Java labels + guard are cleaner |
| PC-dispatch interpretation loop (`while(true){switch(local.pc){…}}`) | uniform, but every proof pays an outer loop invariant + switch unfolding; rejected |
| Direct bytecode → KeY AST frontend | largest effort, no reuse of JavaParser/JML pipeline; rejected |
| Boxed uniform `Object[]` stack | heap-touching pushes/pops pollute frames; fallback only |
| SSA lowering without `Local` ("Mode B") | best proof performance, abandons JML-contracts architecture; future path |
| Structuring *all* control flow in the transpiler (Relooper) | no longer needed: backward restore rule covers unstructured code; structuring stays an optimization |

## 12. Planned File Layout

```
docs/concept-jvm-support.md                              ← this document
key.jvm/                                                 ← new Gradle module (added to settings.gradle)
  build.gradle                                           ← asm, asm-tree, asm-analysis; picocli; api(:key.core)
  src/main/java/org/key_project/jvm/
    Transpiler.java                                      ← facade: Path/byte[] → output folder
    transpiler/ClassFileModel.java, MethodTranspiler.java, ControlFlow.java, Emitter.java …
    rule/GotoSpliceRule.java, GotoRestoreRule.java, IfLiteralRule.java
    profile/JvmProfile.java, JvmProfileResolver.java
    cli/TranspileCli.java
  src/main/resources/org/key_project/jvm/
    runtime/jvm/Local.java                               ← JVM model + JML contracts
    META-INF/services/de.uka.ilkd.key.proof.init.DefaultProfileResolver
  src/test/java/…                                        ← transpile/compile/proof/rule tests
  testdata/…                                             ← .class fixtures, .jml specs, .key problems
```

## 13. KeY Classes This Design Builds On (verified in this codebase)

* Frontend/loading: `JavaService.readCompilationUnit(s)` (`key.core/.../java/JavaService.java`),
  `ProblemInitializer.readJava`, `KeYEnvironment.load`; JML extracted from source comments by
  `transformations/pipeline/JMLTransformer` inside `KeYJavaPipeline`.
* AST: `de.uka.ilkd.key.java.ast.statement.LabeledStatement(Label, Statement)`; statement
  construction via `KeYJavaASTFactory`; program surgery via `JavaTools`
  (`getActiveStatement`, `removeActiveStatement`, `replaceStatement`,
  `getInnermostMethodFrame`), `ProgramElementReplacer`, `JavaBlock.createJavaBlock`,
  `TermBuilder.prog`.
* Rules: `BuiltInRule`/`AbstractBuiltInRuleApp`; template `SetStatementRule` and
  `JmlAssertRule`; registration pattern `WdProfile extends JavaProfile` +
  `WdProfileResolver` + `META-INF/services/…DefaultProfileResolver` (resolved by
  `ProofInitServiceUtil` by profile name).
* Labels: `unusedLabel` taclet strips `#lb: #s` mid-program unless `FreeLabelFinder`
  (matches *any* `Label` node, e.g. from `break L9`) finds the label inside `#s`; `blockEmpty`
  cleans empty blocks; labeled break handled by `blockBreakLabel`/`DoBreak` + loop-scope.
* Original body recovery: `MethodFrame.getExecutionContext().getMethodContext()` →
  `IProgramMethod.getBody()` (`StatementBlock`) — the untouched declared body.
* Contracts: `JMLSpecExtractor` (incl. block contracts on `LabeledStatement`) →
  `SpecificationRepository` → `UseOperationContractRule` (calls in condition/return positions
  via `ProgramContextAdder`).

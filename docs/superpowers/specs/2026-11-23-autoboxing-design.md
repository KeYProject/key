# Autoboxing and Unboxing — Design

**Status:** proposed
**Date:** 2026-11-23
**Branch:** `weigl/autoboxing` (based on `origin/main`)

## Goal

Provide correct support for Java's boxing and unboxing conversions (JLS 5.1.7
and 5.1.8) in KeY, so that code such as

```java
Integer a = 42;
int i = a;
//@ assert i == 42;
```

is parsed, translated, and provable, and so that

```java
Integer a = null;
int i = a;
```

splits into the happy path and a null obligation, exactly like a field access.

## Scope

In scope (all eight wrapper types: `Boolean`, `Byte`, `Short`, `Character`,
`Integer`, `Long`, `Float`, `Double`):

- assignment contexts: local and field initializers, local and field
  assignments, array initializers, array element stores, `return`;
- invocation contexts: method and constructor arguments, including varargs;
- casting contexts: `(Integer) 42`, `(int) integerObj`, `(Object) 42`;
- numeric contexts: unary `+ - ~`, binary arithmetic/bitwise/comparison,
  shifts, array index, `switch` selector;
- conditional expressions (JLS 15.25);
- compound assignment and `++`/`--` on boxed variables.

Out of scope:

- boxing/unboxing inside JML-specification expressions (`requires`, `ensures`,
  `assert`, ...);
- string concatenation conversion;
- `valueOf` cache/identity semantics (only value semantics are modelled);
- unboxing a `Number` variable without an explicit cast (Java does not allow it
  either).

## Current state (verified on `origin/main`)

- Boxing sources that load are not soundly modelled. `Integer a = 42;`
  translates to an assignment of an `int` term into a variable of sort
  `java.lang.Integer`; the proof aborts with
  `TermCreationException` ("elem-update(a) expected `java.lang.Integer`").
- `Integer` in `JavaRedux` has `value`/`valueOf(int)`/`intValue()` with
  contracts, but its static field `TYPE` is uninitialized. The implicit
  non-null invariant for that field can never be discharged, so even
  `Integer.valueOf(42)` blocks every proof. Marking `TYPE` as
  `/*@ nullable @*/` fixes this (verified).
- The other wrappers are incomplete: `Byte` and `Short` are missing entirely;
  `Long`, `Float`, `Double`, `Boolean`, `Character` lack `value`,
  `valueOf(...)` and `...Value()`.
- `MethodCall.assignmentCompatible` explicitly ignores autoboxing.
- Manual desugaring works: after the `TYPE` fix,
  `Integer a = Integer.valueOf(42); int i = a.intValue(); //@ assert i == 42;`
  closes. Reading `a.value` instead of calling `intValue()` also closes.
- Reading a field on a possibly-null receiver already splits into the happy
  path and the null branch (`assignment_read_attribute[_final]`), which throws
  `NullPointerException` under `runtimeExceptions:allow` and yields an
  `a != null` obligation under `runtimeExceptions:ban`.

## Design

### Representation

The front-end desugars conversions to ordinary Java constructs, as javac does:

- **Boxing**: `e` (primitive) becomes `Wrapper.valueOf(<e>)`, for example
  `Integer.valueOf(42)`, `Long.valueOf(1L)`. Boxing only applies when the
  expression already has the wrapper's primitive type; for `Byte`/`Short` an
  in-range `int` constant is narrowed first (`Byte b = 1` becomes
  `Byte.valueOf((byte) 1)`). There is **no widening before boxing**:
  `Long l = 1;` is illegal Java and stays unconverted.
- **Unboxing**: `e` (wrapper) becomes `e.value`, a read of the wrapper's
  `private /*@ spec_public @*/ final <prim> value` field.

Reading `value` is deliberate. It makes unboxing reuse the field-access rules,
which already produce exactly the requested semantics: a happy-path subgoal and
a second subgoal requiring the receiver to be non-null (or throwing
`NullPointerException` when runtime exceptions are allowed). It also avoids
adding new prover rules.

The representation is idempotent: `Wrapper.valueOf(int)` has a primitive
argument (nothing to box), and `e.value` already has the primitive type.

### Conversion engine

A new JavaParser AST transformation, `AutoboxingTransformer`, is added to
`KeYJavaPipeline`. It walks expressions with an optional expected type
(`Target`: primitive, wrapper, or none) supplied by the enclosing context.

Rules:

- Assignment-like contexts supply the target from the declared/assigned type.
- Invocation contexts supply the parameter types from the resolved method or
  constructor; varargs supply the array component type for the remaining
  arguments.
- Cast contexts supply the cast type.
- Numeric contexts unbox numeric operands and widen them to the promoted type
  (JLS 5.6). `==`/`!=` unbox only when at least one operand is a primitive;
  two wrappers remain reference comparison.
- Conditional expressions follow JLS 15.25 (boolean, numeric, reference).
- Unboxing may be followed by a widening primitive conversion, which is made
  explicit with a cast (`long l = intObj` becomes `(long) intObj.value`).
  Boxing is never preceded by a widening conversion.
- Compound assignment `a op= e` on a wrapper becomes
  `a = Wrapper.valueOf((prim) (a.value op e'))`.
- `++`/`--` on a wrapper is rewritten at statement level with a temporary:
  postfix saves the old primitive value before storing the boxed increment,
  prefix stores first and reads afterwards. Where the expression is nested
  among other side-effecting expressions, the enclosing expression is
  linearised in Java evaluation order so the rewrite stays observationally
  equivalent.

The transformer skips JML-specification subtrees. It runs after the structural
builders (`RecordClassBuilder`, `LocalClassTransformation`, `AnnotationMover`)
and before `ConstantStringExpressionEvaluator`.

### Wrapper model

Each wrapper in `key.core/src/main/resources/de/uka/ilkd/key/java/JavaRedux/java/lang/`
gets:

- `private /*@ spec_public @*/ final <prim> value;`
- a `normal_behavior` `valueOf(<prim> v)` contract with
  `ensures \result.value == v; assignable \nothing;` (for `Float`/`Double`,
  use the existing `_isSame` model method so NaN boxes correctly);
- a `normal_behavior` `<prim>Value()` contract with
  `ensures \result == value; assignable \strictly_nothing;`;
- a constructor contract mirroring the existing `Integer` style;
- a `/*@ nullable @*/` annotation on the static `TYPE` field.

`Byte` and `Short` are added from scratch; the other wrappers are completed.

### Acceptance criteria

1. `Integer a = 42; int i = a; //@ assert i == 42;` closes.
2. `Integer a = null; int i = a;` does not silently verify: the field-access
   split produces a happy path and a null subgoal (`a != null` under
   `runtimeExceptions:ban`; an NPE branch under `allow`).
3. `Integer a = 42; int i = a + 1; //@ assert i == 43;` closes.
4. Boxing/unboxing works in method and constructor arguments, including
   varargs, and for all eight wrappers.
5. The Java feature coverage test and the existing suite stay green; the
   coverage documentation is updated.

## Verification strategy

A committed semantic corpus backs every conversion context:

- `key.core/src/test/resources/de/uka/ilkd/key/java/autoboxing/corpus/`
  holds one directory per case: a `.java` file that is valid Java 21 (JML
  comments are ignored by `javac`) *and* loadable by KeY, plus an
  `expected.txt` with the exact runtime output (or `THROWS <exception>`).
- `script/autoboxing/check_java_semantics.sh` compiles each case with
  `javac --release 21`, runs it, and diffs stdout against `expected.txt`,
  including expected exceptions. This records real Java behaviour.
- `AutoboxingSemanticsTest` runs the same cases through KeY and checks the
  recorded verdict: `PROVABLE` (the proof closes), `SPLIT` (the null
  obligation remains), or `UNPROVABLE`.
- Every feature task extends the corpus and runs both sides before its commit.
  Value semantics must agree. Reference identity and `valueOf` caching are
  recorded as known divergences: KeY models value semantics only.

## Risks

- Expression linearisation for `++`/`--` is the riskiest part; it must
  preserve left-to-right evaluation order and single evaluation.
- `value` is a private field; the desugared program will print `a.value` in
  proof goals. KeY does not enforce access control during proofs (verified).
- Float/Double NaN must not be specified with plain `==`.
- The transformer runs over boot classes too; it must be idempotent and must
  not rewrite JML specifications.

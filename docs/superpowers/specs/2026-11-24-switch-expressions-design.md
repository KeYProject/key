# Switch expressions and switch patterns

Status: approved design, ready for an implementation plan.

## Context

KeY currently supports the classic `switch` **statement** (integer, `String`, qualified
`enum` selectors and `case null:`) by keeping a `Switch` node in the Java AST and rewriting
it at proof time:

- `javaRules.key` has a `switch` taclet that replaces `#sw` by `#switchToIf(#sw)`;
- `SwitchToIf` (a `ProgramTransformer`) evaluates the selector once into a temporary,
  builds an `if`-cascade over the case labels, rewrites `break`s into a labelled break, and
  adds a null check for reference selectors.

That path is working (verified by proof: `case null` matches `null`, `String` labels
compare by `==` as before). What is missing:

| Construct | Today |
|---|---|
| switch **expression**, no `yield` (`case 1 -> 10; default -> 0;`) | rejected: `SwitchExpr` unsupported in `JP2KeYConverter` |
| switch **expression** with `yield` | rejected earlier: **Java syntax error**, `yield` is not parsed |
| switch **statement** with type/record patterns or guards | rejected: `TypePatternExpr`/`RecordPatternExpr` (converter crashes or reports unsupported) |
| switch **expression** with patterns | rejected at `SwitchExpr` first |

The probe corpus used to establish this table lives outside the repository (22 cases; see
the plan for the permanent test list).

### Why `yield` does not parse today

KeY configures jmlparser with `ParserConfiguration.LanguageLevel.RAW`, which means "no
language-level validation" (required, because KeY's own JML-annotated bootstrap sources are
rejected by the concrete validators). In jmlparser, `RAW` is `null`, and
`JavaParser#getParserForProvider` enables the `yield` production only if the language level
is non-null and `isYieldSupported()`. Consequently `case 1: yield 10;` is a syntax error.

Switching KeY to a concrete level (`JAVA_21`) was tried and breaks every load with
`'[[JML modifiers]]' is not allowed here`. The fix therefore belongs in the jmlparser fork:
`RAW` must enable `yield` while still skipping validation.

## Goals

- Support switch **expressions** (JEP 361) with arrow and colon arms, `yield`, `throw`
  arms, grouped labels, and the selector kinds the statement form already supports.
- Support type patterns, `when` guards, record patterns, and `case null` inside `switch`,
  for both the statement and the expression form (JEP 440/441).
- Keep symbolic execution Java-correct: the selector is evaluated exactly once, an arm is
  evaluated at most once, `yield` assigns and terminates the arm, and a non-matching arm
  proceeds to the next arm in source order.
- Reject unsupported constructs at load time with a clear message instead of silently
  misbehaving (sound, incomplete).

## Non-goals

- Full JLS dominance/exhaustiveness checking beyond what the front end already enforces.
- Modelling `MatchException` for explicit record accessors (stays rejected, as in the
  pattern stack).
- Changing `String` switch semantics from `==` to `equals`.
- Constant folding of switch expressions (`ConstantExpressionEvaluator`).
- Local classes inside arms, and other unrelated feature gaps.

## Architecture

Approach B from the design discussion: real AST nodes plus a proof-time rewrite that mirrors
`#switchToIf`. Alternatives considered:

- **Pipeline lowering** (javaparser AST rewrite before conversion) — rejected by the user.
- **Converter-level lowering** — same evaluation-order problem, more ad-hoc.

### AST

1. `SwitchExpression extends Expression` with a selector and a branch list.
2. `Yield extends Statement` with a value expression.
3. Branch labels are generalized to carry either a constant expression (`Case`), `default`,
   or a **pattern**: the pattern stack's `Pattern` (`TypePattern`, `RecordPattern`,
   `AnyPattern`) plus an optional guard expression. Arm bodies are statement lists; the
   converter normalizes
   - `case X -> expr;` to a one-statement body `{ yield expr; }`,
   - `case X -> throw e;` to a body with the `throw`,
   - block arms unchanged,
   matching jmlparser's `SwitchEntry.Type` (`EXPRESSION`, `BLOCK`, `THROWS_STATEMENT`,
   `STATEMENT_GROUP`).
4. New visitor operations (`performActionOnSwitchExpression`, `performActionOnYield`) in the
   `Visitor` interface, all implementors (the switch-handling set is
   `CreatingASTVisitor`, `JavaASTVisitor`, `InnerBreakAndContinueReplacer`,
   `OuterBreakContinueAndReturnReplacer`, `PrettyPrinter`, `WhileLoopTransformation`), plus
   child accessors, position/comments, and pretty printing.

### Conversion

- `JP2KeYConverter.visit(SwitchExpr)` builds a `SwitchExpression`; `visit(YieldStmt)`
  builds a `Yield`. Constant labels, `default`, `case null` use the existing conversions.
- Pattern labels reuse the stack's `TypePattern`/`RecordPattern` conversion; the entry's
  `getGuard()` becomes the guard expression.
- Unsupported forms (e.g. a pattern in a context the base branch does not support) are
  reported through `reportUnsupportedElement`.

### Proof-time lowering

- New taclet (working name `switchExpression`):
  `\find(\modality#allmodal{ .. #stm ...})` with a new variable condition
  `\containsSwitchExpression(#stm)` and
  `\replacewith(\modality#allmodal{ .. #lowerSwitchExpression(#stm) ...})`.
- `#lowerSwitchExpression` rewrites the enclosing statement:
  1. introduce a fresh temporary for each switch expression with the `EvaluateArgs.evaluate`
     helper (declaration before the statement, assignment from the selector);
  2. replace each switch expression in the statement by its temporary;
  3. emit a lowered `Switch` statement whose arms assign the temporary
     (`yield e` → `tmp = e; break;`, arrow arms → assignment + break, `throw` arms keep
     throwing);
  4. recurse for nested switch expressions.
- The lowered `Switch` is then handled by the existing `#switchToIf` rule, so selector-once,
  break handling and the null check are shared with statements.
- **Patterns**: pattern labels are lowered in the same place. `SwitchToIf` is extended to
  emit pattern guards (an `instanceof` test with the stack's binding machinery,
  `#declarePatternVars`/`#assumeBinding`) and to `&&` in the `when` guard; a constant label
  keeps the `==` guard. As a consequence pattern switch **statements** work through the same
  path.
- `yield` outside a lowered switch expression is impossible after conversion (front end
  rejects it).

### Evaluation order

The selector-once property comes from the temporary. The remaining order constraint is the
enclosing statement: hoisting a switch expression before earlier, side-effecting
subexpressions of the same statement would reorder evaluation. The first increment supports
a switch expression only when it is the **first-evaluated operand** of the enclosing
statement, e.g.:

- local-variable initializer `int x = switch (…) …;`,
- assignment `x = switch (…) …;`,
- `return switch (…) …;` / `throw new E(switch (…) …);`,
- expression statement `switch (…) …;`,
- `if (switch (…) …)`, `while (switch (…) …)`.

Counter-examples that are rejected with a clear message in the first increment:
`f(g(), switch (…) …)`, `x = f() + switch (…) …`, `if (p() && switch (…) …)`. A later step
in the plan generalizes this by linearizing the preceding subexpressions into temporaries
with the same helper.

## Semantics checklist

- Selector evaluated exactly once.
- Arrow arm value evaluated once, assigned to the result temporary, arm terminated.
- Colon arms keep the source order and fall-through semantics; each `yield` assigns and
  terminates the switch.
- `throw` arms propagate.
- `case null` matches `null` (existing behaviour, verified).
- Enum and `String` selectors behave as in the statement form (`==` for `String`).
- Guards (`when`) are evaluated only after the pattern matched, and only on the current
  selector value.
- Record patterns reuse the stack's `instanceof` record handling, including rejection of
  records with explicit accessors.
- Definite assignment: a switch expression without `default` is accepted only when the
  front end/JLS would accept it (exhaustive enum/sealed); otherwise the construct is
  rejected at load time rather than left uninitialized.

## Testing

- New `SwitchExpressionTest`: every probe case becomes a load-and-prove test.
- `SwitchPatternTest`: type, guard, record, `case null` in statements and expressions.
- Soundness negatives (in the style of `PatternSoundnessTest`): a wrong contract must stay
  open (double evaluation, yield order, guard evaluation).
- Coverage fixtures: move `switch-expression`, `switch-pattern-type`,
  `switch-pattern-record` from `rejected/` to `supported/`; add expression/`yield`/guard/
  `null-default` fixtures; `JavaFeatureCoverageTest` pins them.
- `key-docs` Java Coverage table: switch-expression and pattern-switch rows.
- jmlparser: a parser test that `yield` parses under `LanguageLevel.RAW`.

## Dependencies and sequencing

0. jmlparser: enable `yield` under `RAW`, release, bump `jmltk`.
1. AST nodes and visitor/printer plumbing.
2. Converter for `SwitchExpr`/`YieldStmt` and pattern labels.
3. Lowering meta-construct, taclet, variable condition.
4. Pattern lowering in `SwitchToIf`.
5. Tests, coverage fixtures, documentation.
6. Optional: general evaluation-order linearization.

The work is based on `weigl/pattern-hoisting` (the pattern stack), because pattern switch
depends on `TypePattern`/`RecordPattern` and the binding machinery. When the stack lands,
the branch is rebased onto the merged result.

## Risks

- Evaluation order in arbitrary expression positions; mitigated by the restricted first
  increment and a documented rejection.
- Taclet matching cost for `#stm` + `containsSwitchExpression` over every statement.
- Exhaustiveness/definite assignment; handled conservatively (reject when unsure).
- Cost of the `Visitor` interface change (all implementors), which is why it is a separate,
  mechanical task.
- Continuous rebases while the pattern stack is open.

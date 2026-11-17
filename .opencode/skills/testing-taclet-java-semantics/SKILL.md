---
name: testing-taclet-java-semantics
description: Use when adding or changing a taclet that defines Java semantics (program rules in javaRules.key, integer/float semantics, loop or runtime-exception rules, or a rule selected by a taclet option) and you must show that it still encodes the intended Java semantics.
---

# Testing the Semantics of a Java-Semantics Taclet

## Overview

KeY's Java semantics are taclets in
`key.core/src/main/resources/de/uka/ilkd/key/proof/rules/`. A semantics test must fail when the
taclet's *meaning* changes, not merely when it stops being applicable. The core method is
differential: **instantiate the taclet's `\find`, then compare the behaviour of the matched
program fragment with the behaviour of the fragment it is replaced with.**

The running example is `ifElseUnfold` (`rules/javaRules.key`), which is deliberately more complex
than a simple rewrite: it rewrites a Java `if` statement to another Java program and carries a
freshness guard.

## 1. Understand the taclet and its context

```
ifElseUnfold {
    \find(\modality{#allmodal}{.. if(#nse) #s0 else #s1 ...}\endmodality (post))
    \varcond(\new(#boolv, boolean))
    \replacewith(\modality{#allmodal}{.. boolean #boolv; #boolv = #nse;
                                       if(#boolv) #s0 else{#s1} ...}\endmodality (post))
    \heuristics(simplify_autoname)
}
```

- **Matched fragment**: `if (#nse) #s0 else #s1`. The schema variables' declared types constrain
  instantiation — `#nse` is a `NonSimpleExpression` (it may have side effects), `#s0`/`#s1` are
  statement lists.
- **Replaced fragment**: the same program with the condition hoisted into a fresh `boolean
  #boolv`, and the `else` branch wrapped as a block. The semantics claim is precise: the condition
  is evaluated **exactly once**, in the same state, and neither branch is duplicated.
- **Guards**: `\varcond(\new(#boolv, boolean))` is a freshness guard — the generated variable must
  not capture anything in the program. It belongs in the test even though `\find` matches without
  it. (`\assumes`, `\addrules` and extra goals are the same kind of untested surface.)
- **Context**: the enclosing `\rules(programRules:Java)` gates the taclet on a choice; it is
  simply absent from the rule set if the test input does not select that option. Check
  `rules/optionsDeclarations.key` and pin the choice in `\settings`.
- Related rule files: `javaRules.key` (program rules), `integer/intRules*Semantics.key` (selected
  by `intRules`), `float/`, `loopRules.key`, `loopScopeRules.key`, `runtimeExceptions`, `heapRules.key`.

## 2. Create test candidates from the `\find`

1. Instantiate every schema variable with a **minimal** Java fragment the `\find` accepts:
   `if (b == 0) x = 1; else x = 2;`.
2. Add candidates for each guard, not only the happy path:
   - a **side-effecting** condition (`if (i++ == 0) ...`) — pins exactly-once evaluation;
   - a program that already declares `boolean boolv;` — pins the `\new` freshness guard;
   - a non-block `else` body — pins the `else{#s1}` wrapping.
3. Verify the candidate actually triggers the rule: query the goal's rule app index for the
   taclet name (`TestRuleAppIndexMode` shows the API). A candidate that never matches proves
   nothing.
4. Some rules only match in a specific program context (behind a method-frame prefix, inside a
   loop body, …). If no Java source can produce the matched fragment, the crafted-goal white-box
   test is the only honest gate.

## 3. Compare matched vs replaced behaviour

Write two inputs that differ only in the fragment under test, and prove the **same
postcondition** on both:

| | matched program | replaced program |
|---|---|---|
| condition | `if (b == 0) x = 1; else x = 2;` | `boolean v = (b == 0); if (v) x = 1; else { x = 2; }` |
| true postcondition | closes | closes |
| false postcondition (e.g. `x == 1` for all `b`) | stays open | stays open |

For `ifElseUnfold` the side-effect candidate is the decisive pair: with `if (i++ == 0) ...`, the
replaced program must increment `i` exactly once. If the taclet evaluated the condition twice (or
duplicated a branch), the two proofs diverge on `i`'s value even though both still close.

Assert the remaining open goal's formula, not only its count, so both sides fail at the same
point. Because a proof can close through *sibling* rules (`ifElse`, `if`, `ifElseSplit`), also
walk the finished proof and assert that a `RuleApp` of `ifElseUnfold` occurs — otherwise the
positive case may never have used the rule.

## 4. White box: apply the named taclet

When the rule name matters (a black-box proof may close through another rule), apply it directly:

```java
PosInOccurrence pos =
    new PosInOccurrence(goal.sequent().antecedent().getFirst(), PosInTerm.getTopLevel(), true);
TacletApp app = goal.ruleAppIndex()
        .getTacletAppAt(TacletFilter.TRUE, pos, goal.proof().getServices()).stream()
        .filter(a -> a.taclet().name().toString().equals("ifElseUnfold"))
        .findFirst().orElseThrow();
ImmutableList<Goal> goals = goal.apply(app);
assertThat(goals).hasSize(1);   // assert the resulting sequent — it is the replacement
```

Assert the replacement, not just the goal count: the resulting term must contain
`boolean <v>; <v> = b == 0; if (<v>) x = 1; else { x = 2; }` with a fresh `<v>`. Apply the rule to
two goals (or after pruning) and assert the names differ — that is the `\new` guard. Saved proofs
show the instantiation explicitly: `(rule "ifElseUnfold" (formula "5") (term "1") (inst "#boolv=x"))`.

## 5. Make the test capable of failing

Mutate the taclet and confirm the test fails; then revert. For `ifElseUnfold`:

| mutation | fails |
|---|---|
| swap `#s0` and `#s1` | the true-postcondition pair (branches prove the wrong result) |
| drop the `else{#s1}` block (`else #s1`) | the white-box assertion on the replacement term |
| `#boolv = #nse` → `#boolv = TRUE` | the false-postcondition pair and the side-effect pair |
| remove the `\new` varcond (reuse the program's `boolv`) | the freshness assertion and the name-clash candidate |

A test that survives the mutation does not test the semantics. Negative cases must fail *because
of the semantics*: minimise the program until the semantic condition is the only open goal.

## 6. Gates

```
./gradlew :key.core:test --tests "*<YourTest>"
./gradlew :key.core:spotlessCheck
./gradlew -DENABLE_NULLNESS=true compileTestJava
```

JUnit 5 + AssertJ. Do not tag these tests `owntest`, `interactive` or `performance`.

## Common mistakes

| Symptom | Cause |
|---|---|
| Candidate never applies the rule | instantiation is outside the `\find` pattern or the choice in `\settings` is missing |
| Positive proof closes with the taclet disabled | the proof never needed the rule; assert a `RuleApp` of that taclet in the proof |
| Matched and replaced programs both close, but the taclet is wrong | postcondition is too weak; also run the negative pair and the guard candidates (`\varcond`, `\assumes`) |
| Negative case leaves several open goals | the program is wrong for another reason; minimise it |
| Stored `.proof` no longer reloads after a rule change | expected — regenerate it from a closed run with the same `\settings` |
| Taclet-equality or pretty-printer tests pass although the rule changed | `PrettyPrinter.performActionOnContextStatementBlock` drops the execution context (see `taclets.old.txt`), so context changes are invisible there; assert the applied rule and the resulting term instead |

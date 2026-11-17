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

## 1. Understand the taclet and its context

Read the declaration before writing any test:

```
assignment {
    \find(\modality{#allmodal}{.. #loc = #se; ...}\endmodality (post))
    \replacewith({#loc := #se}\modality{#allmodal}{.. ...}\endmodality (post))
    \heuristics(simplify_prog, simplify_prog_subset)
}
```

- **Matched fragment**: the part of the `\find` term that is program (`.. #loc = #se; ...`) plus
  the schema variables (`#loc`, `#se` — their declared types constrain what may instantiate them).
- **Context statement blocks** (`.#pm@#t(#v)..`) bind schema variables to the innermost
  `MethodFrame`'s execution context; the receiver (`#v`) is the frame's variable, which need not
  be `this` — the replacement then stores into that variable.
- **Replaced fragment**: the same program with the rewrite applied — usually an update
  (`{#loc := #se}`) that carries the effect into the postcondition.
- **Guards**: `\assumes`, `\varcond`, `\addrules` and additional goals are part of the semantics;
  a test that only covers the happy path misses them.
- **Context**: the enclosing `\rules(programRules:Java, permissions:off)` gates the taclet on a
  choice. The taclet is simply absent if the test input does not select that option — check
  `rules/optionsDeclarations.key` and pin the choice in `\settings`.
- Related rule files: `javaRules.key` (program rules), `integer/intRules*Semantics.key` (selected
  by `intRules`), `float/`, `loopRules.key`, `loopScopeRules.key`, `runtimeExceptions`, `heapRules.key`.

## 2. Create test candidates from the `\find`

1. Instantiate every schema variable with a **minimal** Java fragment the `\find` accepts
   (`int x; x = 5;` for the assignment rule).
2. Verify the candidate actually triggers the rule: query the goal's rule app index for the
   taclet name (`TestRuleAppIndexMode` shows the API). A candidate that never matches proves
   nothing.
3. Vary the context along the schema-variable types: local vs field, `this[#se] = #se0` access,
   arrays, permissions on/off. Each variant gets its own positive/negative pair.
4. Some rules only match in a specific program context. Example:
   `assignment_write_array_this_access_normalassign` matches `this[i] = v;` only **behind a
   method-frame prefix** (the implicit `$prepare()` body generated for array initialisation), so
   no ordinary Java source triggers it. Drive such a rule through the implicit method or a
   crafted `method-frame(...)` goal (`TestMatchTaclet#testPrefixMatching`), and say so in the
   test's javadoc.
5. If no Java source can produce the matched fragment, a black-box pair is impossible: the
   crafted-goal white-box test is then the only honest gate, and the "replaced" side is the
   instantiated `\replacewith` term you assert on the resulting goal.

## 3. Compare matched vs replaced behaviour

Write two inputs that differ only in the fragment under test:

- **matched**: the program containing the `\find` fragment (e.g. `\<{ int x; x = 5; }\> post`);
- **replaced**: the same program with the replacement written out
  (e.g. `{x := 5} \<{ int x; }\> post`).

Prove the **same postcondition** on both:

| Postcondition | Matched | Replaced | Conclusion |
|---|---|---|---|
| true under Java semantics | closes | closes | rule preserves semantics |
| false under Java semantics | stays open | stays open | rule does not over-approximate |

Diverging outcomes mean the taclet is not semantics-preserving (or the replacement was written
wrongly). Assert the remaining open goal's formula, not only its count, so both sides fail at the
same point.

Because a proof can close through *sibling* rules (the array-initialisation loop can close the
same goal as the array-write rule), also walk the finished proof and assert that a `RuleApp` of
the taclet under test occurs — otherwise the positive case may never have used it.

## 4. White box: apply the named taclet

When the rule name matters (a black-box proof may close through another rule), apply it directly:

```java
PosInOccurrence pos =
    new PosInOccurrence(goal.sequent().antecedent().getFirst(), PosInTerm.getTopLevel(), true);
TacletApp app = goal.ruleAppIndex()
        .getTacletAppAt(TacletFilter.TRUE, pos, goal.proof().getServices()).stream()
        .filter(a -> a.taclet().name().toString().equals("assignment"))
        .findFirst().orElseThrow();
ImmutableList<Goal> goals = goal.apply(app);
assertThat(goals).hasSize(1);   // and assert the resulting sequent — it is the replacement
```

## 5. Make the test capable of failing

Mutate the taclet (swap a branch, drop a side condition, invert the update) and confirm the test
fails; then revert. A test that survives the mutation does not test the semantics. Negative cases
must fail *because of the semantics*: minimise the program until the semantic condition is the
only open goal.

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
| Matched and replaced programs both close, but the taclet is wrong | postcondition is too weak; also run the negative pair and the `\assumes` boundary |
| Negative case leaves several open goals | the program is wrong for another reason; minimise it |
| Stored `.proof` no longer reloads after a rule change | expected — regenerate it from a closed run with the same `\settings` |
| Taclet-equality or pretty-printer tests pass although the rule changed | `PrettyPrinter.performActionOnContextStatementBlock` drops the execution context (see `taclets.old.txt`), so context changes are invisible there; assert the applied rule and the resulting term instead |

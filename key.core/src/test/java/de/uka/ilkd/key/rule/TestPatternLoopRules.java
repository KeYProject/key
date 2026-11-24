/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.rule;

import java.util.ArrayList;
import java.util.List;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.nparser.KeyIO;
import de.uka.ilkd.key.proof.*;
import de.uka.ilkd.key.proof.calculus.JavaDLSequentKit;
import de.uka.ilkd.key.proof.init.*;
import de.uka.ilkd.key.proof.io.KeYFileForTests;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.proof.io.RuleSource;
import de.uka.ilkd.key.proof.io.RuleSourceFactory;
import de.uka.ilkd.key.util.HelperClassForTests;

import org.key_project.logic.PosInTerm;
import org.key_project.prover.proof.rulefilter.TacletFilter;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.util.collection.ImmutableList;

import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;

import static de.uka.ilkd.key.logic.equality.RenamingTermProperty.RENAMING_TERM_PROPERTY;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Tests the pattern-aware {@code if} decomposition rules of the production rule file
 * {@code javaRules.key}:
 *
 * <ul>
 * <li>{@code ifUnfoldPattern}/{@code ifElseUnfoldPattern} evaluate a guard that binds pattern
 * variables and declare the bound variables in the branches where they are definitely bound</li>
 * <li>{@code ifUnfold}/{@code ifElseUnfold} must not match such guards, because they would drop the
 * declarations of the pattern variables</li>
 * </ul>
 *
 * <p>
 * The pattern rules replace the generic rules only for binding guards; non-binding guards are still
 * handled by {@code ifUnfold}/{@code ifElseUnfold}.
 */
class TestPatternLoopRules {

    /**
     * A profile whose standard rules are the LDT declarations plus {@code javaRules.key}, the
     * file containing the rules under test.
     */
    private static final Profile PROFILE = new JavaProfile() {
        @Override
        public RuleCollection getStandardRules() {
            return new RuleCollection(
                ImmutableList.of(RuleSourceFactory.fromDefaultLocation(RuleSource.ldtFile),
                    RuleSourceFactory.fromDefaultLocation("ruleSetsDeclarations.key"),
                    RuleSourceFactory.fromDefaultLocation("javaRules.key")),
                ImmutableList.nil());
        }
    };

    private static InitConfig initConfig;
    private static Services services;
    private static TacletIndex allRules;

    @BeforeAll
    static void setUp() {
        try {
            var envInput = new KeYFileForTests(
                "TestPatternLoopRules", HelperClassForTests.DUMMY_KEY_FILE, PROFILE);
            initConfig = new ProblemInitializer(PROFILE).prepare(envInput);
        } catch (Exception e) {
            throw e instanceof RuntimeException re ? re : new RuntimeException(e);
        }
        services = initConfig.getServices();
        allRules = initConfig.createTacletIndex();
    }


    private static JTerm parseTerm(String term) {
        return new KeyIO(services, initConfig.namespaces()).parseExpression(term);
    }

    /**
     * Creates a goal {@code ==> \\<{ program }\\> true} whose rule set contains only the given
     * rule,
     * applies the rule at the top level of the succedent and returns the single successor goal.
     */
    private Goal applyRule(String ruleName, String program) {
        Goal goal = createGoal(program, singleRuleIndex(ruleName));
        var pos = topLevelPosition(goal);
        var apps = goal.ruleAppIndex().getTacletAppAt(TacletFilter.TRUE, pos, services);
        assertEquals(1, apps.size(),
            "Expected exactly one application of " + ruleName + " at " + pos + ", but found:\n"
                + apps);
        var app = apps.head().tryToInstantiate(services);
        assertNotNull(app, "Rule application of " + ruleName + " could not be completed");
        assertTrue(app.complete(), "Rule application of " + ruleName + " should be complete");

        ImmutableList<Goal> goals = app.taclet().getExecutor().apply(goal, app);
        assertEquals(1, goals.size(), "Applying " + ruleName + " should create a single goal");
        return goals.head();
    }

    /**
     * Returns the names of all rules that are applicable at the top level of the given program.
     */
    private List<String> applicableRules(String program) {
        Goal goal = createGoal(program, allRules);
        List<String> names = new ArrayList<>();
        for (TacletApp app : goal.ruleAppIndex()
                .getTacletAppAt(TacletFilter.TRUE, topLevelPosition(goal), services)) {
            names.add(app.taclet().name().toString());
        }
        return names;
    }

    private static TacletIndex singleRuleIndex(String ruleName) {
        var taclet = allRules.lookup(ruleName);
        assertNotNull(taclet, "rule " + ruleName + " not found in javaRules.key");
        var tacletIndex = TacletIndexKit.getKit().createTacletIndex();
        tacletIndex.add(taclet);
        return tacletIndex;
    }

    private static Goal createGoal(String program, TacletIndex tacletIndex) {
        var succ =
            ImmutableList.singleton(new SequentFormula(parseTerm("\\<{" + program + "}\\> true")));
        var sequent = JavaDLSequentKit.createSequent(ImmutableList.nil(), succ);
        var proof = new Proof("TestPatternLoopRules", initConfig.deepCopy());
        proof.setRoot(new Node(proof, sequent));
        return new Goal(proof.root(), tacletIndex,
            new BuiltInRuleAppIndex(new BuiltInRuleIndex()), proof.getServices());
    }

    private static PosInOccurrence topLevelPosition(Goal goal) {
        return new PosInOccurrence(goal.sequent().succedent().getFirst(),
            PosInTerm.getTopLevel(), false);
    }

    private static void assertSuccedent(Goal goal, String expectedFormula) {
        JTerm actual = (JTerm) goal.sequent().succedent().getFirst().formula();
        final JTerm expected = parseTerm(expectedFormula);
        assertTrue(RENAMING_TERM_PROPERTY.equalsModThisProperty(actual, expected),
            "Expected succedent:\n" + ProofSaver.printAnything(expected, services)
                + "\nBut was:\n" + ProofSaver.printAnything(actual, services));
    }

    @Test
    void appliesToBindingWhile() {
        List<String> rules = applicableRules(
            "while (new String(\"x\") instanceof String s) { int y = s.length(); }");
        assertTrue(rules.contains("patternLoopUnfold"), rules.toString());
    }

    @Test
    void ignoresPlainWhile() {
        List<String> rules = applicableRules(
            "while (new String(\"x\") != null) { int y = 1; }");
        assertFalse(rules.contains("patternLoopUnfold"), rules.toString());
    }

    /**
     * The rewritten loop has a plain boolean guard, so the pattern rule must not fire on it again.
     */
    @Test
    void doesNotRefireOnRewrittenLoop() {
        List<String> rules = applicableRules("boolean b; while (b) { int y = 1; }");
        assertFalse(rules.contains("patternLoopUnfold"), rules.toString());
        assertFalse(rules.contains("patternLoopUnfoldNested"), rules.toString());
    }

    @Test
    void rewritesWhileWithSingleEvaluation() {
        Goal goal = applyRule("patternLoopUnfold",
            "while (new String(\"x\") instanceof String s) { int y = s.length(); }");
        assertSuccedent(goal, """
                \\<{
                  java.lang.String subj;
                  boolean b;
                  subj = new String("x");
                  b = subj instanceof String;
                  while (b) {
                    java.lang.String s = (String) subj;
                    loop:
                    {
                      int y = s.length();
                    }
                    subj = new String("x");
                    b = subj instanceof String;
                  }
                }\\> true
                """);
    }

    /**
     * A tested expression with side effects is evaluated exactly once per guard evaluation: once
     * before the loop and once at the body-end refresh, and the binding uses the temporary.
     */
    @Test
    void evaluatesTestedMethodCallOncePerGuardEvaluation() {
        Goal goal = applyRule("patternLoopUnfold",
            "while (this.toString() instanceof String s) { int y = 1; }");
        String printed = ProofSaver.printAnything(
            goal.sequent().succedent().getFirst().formula(), services);
        assertEquals(2, countOccurrences(printed, "this.toString()"), printed);
        assertTrue(printed.contains("subj = this.toString();"), printed);
        assertFalse(printed.contains("(String) this.toString()"), printed);
    }

    @Test
    void addsAfterLoopBindingForNegatedGuard() {
        Goal goal = applyRule("patternLoopUnfold",
            "while (!(new String(\"x\") instanceof String s)) { int y = 1; }"
                + " int z = s.length();");
        assertSuccedent(goal, """
                \\<{
                  java.lang.String subj;
                  boolean b;
                  subj = new String("x");
                  b = !(subj instanceof String);
                  while (b) {
                    loop:
                    {
                      int y = 1;
                    }
                    subj = new String("x");
                    b = !(subj instanceof String);
                  }
                  java.lang.String s = (String) subj;
                  int z = s.length();
                }\\> true
                """);
    }

    @Test
    void suppressesAfterLoopBindingOnBreak() {
        Goal goal = applyRule("patternLoopUnfold",
            "while (!(new String(\"x\") instanceof String s)) { break; }");
        assertSuccedent(goal, """
                \\<{
                  java.lang.String subj;
                  boolean b;
                  subj = new String("x");
                  b = !(subj instanceof String);
                  while (b) {
                    loop:
                    {
                      break;
                    }
                    subj = new String("x");
                    b = !(subj instanceof String);
                  }
                }\\> true
                """);
    }

    /**
     * A continue leaves the body's labeled block, so the guard refresh runs after any enclosing
     * finally block instead of inside it.
     */
    @Test
    void refreshesGuardOutsideFinallyAfterContinue() {
        Goal goal = applyRule("patternLoopUnfold",
            "while (this.toString() instanceof String s) {"
                + " try { continue; } finally { int z = 1; } }");
        assertSuccedent(goal, """
                \\<{
                    java.lang.Object subj;
                    boolean b;
                    subj = this.toString();
                    b = subj instanceof String;
                    while (b) {
                      java.lang.String s = (String) subj;
                      loop:
                      {
                        try {
                          break loop;
                        } finally {
                          int z = 1;
                        }
                      }
                      subj = this.toString();
                      b = subj instanceof String;
                    }
                  }\\> true
                """);
    }

    @Test
    void rewritesForWithAssignmentInitializerAndAfterBinding() {
        Goal goal = applyRule("patternLoopUnfold",
            "int i; for (i = 0; !(this.toString() instanceof String s); i++) { }"
                + " int z = s.length();");
        assertSuccedent(goal, """
                \\<{
                    int i;
                    java.lang.Object subj;
                    boolean b;
                    {
                      i = 0;
                      subj = this.toString();
                      b = !(subj instanceof String);
                      while (b) {
                        loop:
                        {}
                        i++;
                        subj = this.toString();
                        b = !(subj instanceof String);
                      }
                    }
                    java.lang.String s = (String) subj;
                    int z = s.length();
                  }\\> true
                """);
    }

    @Test
    void rewritesForWithContinueAndUpdate() {
        Goal goal = applyRule("patternLoopUnfold",
            "for (int i = 0; i < 3 && this.toString() instanceof String s; i++) {"
                + " if (i == 1) { continue; } }");
        assertSuccedent(goal, """
                \\<{
                    java.lang.Object subj;
                    boolean b;
                    {
                      int i = 0;
                      subj = this.toString();
                      b = i < 3 && subj instanceof String;
                      while (b) {
                        java.lang.String s = (String) subj;
                        loop:
                        {
                          if (i == 1) {
                            break loop;
                          }
                        }
                        i++;
                        subj = this.toString();
                        b = i < 3 && subj instanceof String;
                      }
                    }
                  }\\> true
                """);
    }

    @Test
    void rewritesDoWithBreak() {
        Goal goal = applyRule("patternLoopUnfold",
            "do { break; } while (this.toString() instanceof String s);");
        assertSuccedent(goal, """
                \\<{
                    java.lang.Object subj;
                    boolean b;
                    outer:
                    {
                      {
                        break outer;
                      }
                      {
                        subj = this.toString();
                        b = subj instanceof String;
                        while (b) {
                          java.lang.String s = (String) subj;
                          loop:
                          {
                            break;
                          }
                          subj = this.toString();
                          b = subj instanceof String;
                        }
                      }
                    }
                  }\\> true
                """);
    }

    @Test
    void rewritesDoWithContinue() {
        Goal goal = applyRule("patternLoopUnfold",
            "do { continue; } while (this.toString() instanceof String s);");
        assertSuccedent(goal, """
                \\<{
                    java.lang.Object subj;
                    boolean b;
                    {
                      inner:
                      {
                        break inner;
                      }
                      {
                        subj = this.toString();
                        b = subj instanceof String;
                        while (b) {
                          java.lang.String s = (String) subj;
                          loop:
                          {
                            break loop;
                          }
                          subj = this.toString();
                          b = subj instanceof String;
                        }
                      }
                    }
                  }\\> true
                """);
    }

    @Test
    void rewritesNestedBlockBindingLoop() {
        Goal goal = applyRule("patternLoopUnfoldNested",
            "{ while (new String(\"x\") instanceof String s) { int y = s.length(); } }");
        assertSuccedent(goal, """
                \\<{
                    {
                      java.lang.String subj;
                      boolean b;
                      subj = new String("x");
                      b = subj instanceof String;
                      while (b) {
                        java.lang.String s = (String) subj;
                        loop:
                        {
                          int y = s.length();
                        }
                        subj = new String("x");
                        b = subj instanceof String;
                      }
                    }
                  }\\> true
                """);
    }

    private static int countOccurrences(String text, String search) {
        int count = 0;
        for (int i = text.indexOf(search); i >= 0; i = text.indexOf(search, i + 1)) {
            count++;
        }
        return count;
    }
}

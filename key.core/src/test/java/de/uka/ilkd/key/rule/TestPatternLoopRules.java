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
import de.uka.ilkd.key.util.parsing.BuildingException;

import org.key_project.logic.PosInTerm;
import org.key_project.prover.proof.rulefilter.TacletFilter;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.util.collection.ImmutableList;

import org.junit.jupiter.api.Assumptions;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

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
    private static final Logger LOGGER = LoggerFactory.getLogger(TestPatternLoopRules.class);

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
            if (isMetaConstructParserGap(e)) {
                String reason = "javaRules.key cannot be loaded, because the jmlparser does not"
                    + " support the #posBinding/#negBinding program meta-constructs yet: "
                    + e.getMessage();
                LOGGER.warn("Skipping the pattern-loop rule tests. {}", reason);
                Assumptions.assumeTrue(false, reason);
            }
            throw e instanceof RuntimeException re ? re : new RuntimeException(e);
        }
        services = initConfig.getServices();
        allRules = initConfig.createTacletIndex();
    }

    private static boolean isMetaConstructParserGap(Throwable error) {
        for (Throwable t = error; t != null; t = t.getCause()) {
            if (t instanceof BuildingException) {
                String message = t.getMessage();
                if (message != null
                        && (message.contains("#posBinding") || message.contains("#negBinding"))) {
                    return true;
                }
            }
        }
        return false;
    }

    private static JTerm parseTerm(String term) {
        return new KeyIO(services, initConfig.namespaces()).parseExpression(term);
    }

    /**
     * Creates a goal {@code ==> \<{ program }\> true} whose rule set contains only the given rule,
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
        JTerm expected = parseTerm(expectedFormula);
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

    @Test
    void rewritesBodyWithPositionAndGuardRefresh() {
        Goal goal = applyRule("patternLoopUnfold",
            "while (new String(\"x\") instanceof String s) { int y = s.length(); }");
        assertSuccedent(goal,
            "\\<{boolean b = new String(\"x\") instanceof String s;"
                + " while (b) { java.lang.String s = (String) new String(\"x\");"
                + " int y = s.length(); b = new String(\"x\") instanceof String; }}\\> true");
    }

    @Test
    void addsAfterLoopBindingForNegatedGuard() {
        Goal goal = applyRule("patternLoopUnfold",
            "while (!(new String(\"x\") instanceof String s)) { int y = 1; }"
                + " int z = s.length();");
        assertSuccedent(goal,
            "\\<{boolean b = !(new String(\"x\") instanceof String s);"
                + " while (b) { int y = 1; b = !(new String(\"x\") instanceof String); }"
                + " java.lang.String s = (String) new String(\"x\");"
                + " int z = s.length();}\\> true");
    }

    @Test
    void suppressesAfterLoopBindingOnBreak() {
        Goal goal = applyRule("patternLoopUnfold",
            "while (!(new String(\"x\") instanceof String s)) { break; }");
        assertSuccedent(goal,
            "\\<{boolean b = !(new String(\"x\") instanceof String s);"
                + " while (b) { break; b = !(new String(\"x\") instanceof String); }}\\> true");
    }


    @Test
    void rewritesForBodyAndUpdate() {
        Goal goal = applyRule("patternLoopUnfold",
            "for (int i = 0; i < 1 && new String(\"x\") instanceof String s; i++) {"
                + " int y = s.length(); }");
        String printed = ProofSaver.printAnything(
            goal.sequent().succedent().getFirst().formula(), services);
        assertTrue(printed.contains("while (b)"), printed);
        assertTrue(printed.contains("s = (String) new String(\"x\")"), printed);
    }

    @Test
    void doesNotLeakForInitVariables() {
        Goal goal = applyRule("patternLoopUnfold",
            "for (int i = 0; i < 1 && new String(\"x\") instanceof String s; i++) { }");
        String printed = ProofSaver.printAnything(
            goal.sequent().succedent().getFirst().formula(), services);
        assertTrue(printed.contains("int i = 0;"), printed);
    }

    @Test
    void rewritesDoBodyButNotFirstBody() {
        Goal goal = applyRule("patternLoopUnfold",
            "do { int y = 1; } while (!(new String(\"x\") instanceof String s));");
        String printed = ProofSaver.printAnything(
            goal.sequent().succedent().getFirst().formula(), services);
        assertTrue(printed.indexOf("int y = 1;") < printed.indexOf("java.lang.String s"),
            printed);
    }

    @Test
    void refreshesGuardBeforeContinue() {
        Goal goal = applyRule("patternLoopUnfold",
            "while (new String(\"x\") instanceof String s) { continue; }");
        String printed = ProofSaver.printAnything(
            goal.sequent().succedent().getFirst().formula(), services);
        assertTrue(printed.matches(
            "(?s).*b = new String\\(\"x\"\\) instanceof String;\\s+continue;.*"),
            printed);
    }
}

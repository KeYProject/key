/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.rule;

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
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Tests the pattern-assignment taclets of the production rule file {@code javaRules.key}, which
 * decompose assignments whose initializer binds pattern variables:
 *
 * <ul>
 * <li>{@code instanceofPatternAssignmentSE/NSE}: {@code b = e instanceof T v;} is rewritten to
 * {@code b = e instanceof T;} (the binding is not relevant for a plain assignment)</li>
 * <li>{@code andPatternAssignment}/{@code orPatternAssignment}: the guard expression is evaluated
 * once into a fresh boolean variable; in the branch where the guard is known to have matched the
 * pattern variables are declared by {@code #posBinding}</li>
 * <li>{@code notPatternAssignment}: the guard is evaluated into a fresh boolean variable and
 * negated</li>
 * <li>{@code conditionalPatternAssignment}: the condition of a ternary is evaluated into a fresh
 * boolean variable; the branches declare the pattern variables bound by {@code #posBinding} (resp.
 * {@code #negBinding})</li>
 * </ul>
 *
 * <p>
 * All six rules are loaded from the production rule file {@code javaRules.key} (there are no
 * test-only copies). Loading this file requires the jmlparser to support the
 * {@code #posBinding}/{@code #negBinding} program meta-constructs; until the parser supports them
 * the rule base cannot be loaded and all tests of this class are skipped (see {@link #setUp()}).
 */
class TestPatternAssignmentRules {
    private static final Logger LOGGER = LoggerFactory.getLogger(TestPatternAssignmentRules.class);

    /**
     * A profile whose standard rules are the LDT declarations plus {@code javaRules.key}, the
     * file containing the pattern assignment rules under test.
     */
    private static final Profile PROFILE = new JavaProfile() {
        @Override
        public RuleCollection getStandardRules() {
            return new RuleCollection(
                ImmutableList.of(RuleSourceFactory.fromDefaultLocation(RuleSource.ldtFile),
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
                "TestPatternAssignmentRules", HelperClassForTests.DUMMY_KEY_FILE, PROFILE);
            initConfig = new ProblemInitializer(PROFILE).prepare(envInput);
        } catch (Exception e) {
            if (isMetaConstructParserGap(e)) {
                String reason = "javaRules.key cannot be loaded, because the jmlparser does not"
                    + " support the #posBinding/#negBinding program meta-constructs yet: "
                    + e.getMessage();
                LOGGER.warn("Skipping the pattern-assignment rule tests. {}", reason);
                Assumptions.assumeTrue(false, reason);
            }
            throw e instanceof RuntimeException re ? re : new RuntimeException(e);
        }
        services = initConfig.getServices();
        allRules = initConfig.createTacletIndex();
    }

    /**
     * Checks whether the given exception chain contains the parse error caused by the jmlparser
     * not knowing the {@code #posBinding}/{@code #negBinding} meta-constructs, in which case it
     * tries to resolve them as schema variables.
     */
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
     * Creates a goal {@code ==> \<{ program }\> true} whose rule set contains only the given rule
     * and applies the rule at the top level of the succedent. Asserts that there is exactly one
     * complete application and that it produces exactly one successor goal, which is returned.
     */
    private Goal applyRule(String ruleName, String program) {
        var succ =
            ImmutableList.singleton(new SequentFormula(parseTerm("\\<{" + program + "}\\> true")));
        var sequent = JavaDLSequentKit.createSequent(ImmutableList.nil(), succ);
        var proof = new Proof("TestPatternAssignmentRules", initConfig.deepCopy());
        proof.setRoot(new Node(proof, sequent));

        var taclet = allRules.lookup(ruleName);
        assertNotNull(taclet, "rule " + ruleName + " not found in javaRules.key");
        var tacletIndex = TacletIndexKit.getKit().createTacletIndex();
        tacletIndex.add(taclet);
        var goal = new Goal(proof.root(), tacletIndex,
            new BuiltInRuleAppIndex(new BuiltInRuleIndex()), proof.getServices());

        var pos =
            new PosInOccurrence(goal.sequent().succedent().getFirst(), PosInTerm.getTopLevel(),
                false);
        var apps = goal.ruleAppIndex().getTacletAppAt(TacletFilter.TRUE, pos, services);
        assertEquals(1, apps.size(),
            "Expected exactly one application of " + ruleName + " at " + pos + ", but found:\n"
                + apps);
        var app = apps.head();
        assertTrue(app.complete(), "Rule application of " + ruleName + " should be complete");

        ImmutableList<Goal> goals = app.taclet().getExecutor().apply(goal, app);
        assertEquals(1, goals.size(), "Applying " + ruleName + " should create a single goal");
        return goals.head();
    }

    /**
     * Asserts that the succedent of the goal consists of a single formula that is equal to the
     * parsed expected formula modulo bound renaming, i.e. the programs are the same up to the
     * names of the (locally declared) program variables.
     */
    private static void assertSuccedent(Goal goal, String expectedFormula) {
        JTerm actual = (JTerm) goal.sequent().succedent().getFirst().formula();
        JTerm expected = parseTerm(expectedFormula);
        assertTrue(RENAMING_TERM_PROPERTY.equalsModThisProperty(actual, expected),
            "Expected succedent:\n" + ProofSaver.printAnything(expected, services)
                + "\nBut was:\n" + ProofSaver.printAnything(actual, services));
    }

    @Test
    void instanceofPatternAssignmentSE() {
        var goal = applyRule("instanceofPatternAssignmentSE",
            "Object o; boolean b = o instanceof String s;");
        // the pattern variable s is dropped, the right hand side becomes a plain instanceof
        assertSuccedent(goal, "\\<{Object o; boolean b = o instanceof String;}\\> true");
    }

    @Test
    void instanceofPatternAssignmentNSE() {
        var goal = applyRule("instanceofPatternAssignmentNSE",
            "Object o; boolean b = (o == null ? o : o) instanceof String s;");
        assertSuccedent(goal,
            "\\<{Object o; boolean b = (o == null ? o : o) instanceof String;}\\> true");
    }

    @Test
    void andPatternAssignment() {
        var goal = applyRule("andPatternAssignment",
            "Object o; boolean b = o instanceof String s && o == null;");
        // The guard is evaluated once into a fresh boolean variable; the second operand is
        // evaluated only in the branch where the guard is known to have matched, where the
        // pattern variable s is additionally declared by #posBinding.
        assertSuccedent(goal,
            "\\<{Object o; boolean b; boolean b_1; { b_1 = o instanceof String s; }"
                + " if (b_1) { String s = (String) o; b = o == null; } else { b = false; }}\\> true");
    }

    @Test
    void orPatternAssignment() {
        var goal = applyRule("orPatternAssignment",
            "Object o; boolean b = o instanceof String s || o == null;");
        // The guard is evaluated once into a fresh boolean variable; the second operand is
        // evaluated only if the guard is false, in which case b is the value of the second
        // operand.
        assertSuccedent(goal,
            "\\<{Object o; boolean b; boolean b_1; { b_1 = o instanceof String s; }"
                + " if (b_1) { b = true; } else { b = o == null; }}\\> true");
    }

    @Test
    void notPatternAssignment() {
        var goal = applyRule("notPatternAssignment",
            "Object o; boolean b = !(o instanceof String s);");
        // The guard is evaluated into a fresh boolean variable and negated; no branch is
        // introduced, hence no pattern variable is declared.
        assertSuccedent(goal,
            "\\<{Object o; boolean b; boolean b_1; { b_1 = (o instanceof String s); } b = !b_1;}"
                + "\\> true");
    }

    @Test
    void conditionalPatternAssignment() {
        var goal = applyRule("conditionalPatternAssignment",
            "Object o; boolean r = !(o instanceof String s) ? o != null : o == null;");
        // The negated guard binds s only when it evaluates to false, hence s is declared in the
        // else-branch by #negBinding; in the then-branch no pattern variable is bound.
        assertSuccedent(goal,
            "\\<{Object o; boolean r; boolean b; { b = !(o instanceof String s); }"
                + " if (b) { r = o != null; } else { String s = (String) o; r = o == null; }}\\>"
                + " true");
    }
}

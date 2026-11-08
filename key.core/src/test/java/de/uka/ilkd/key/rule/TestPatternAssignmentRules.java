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

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Tests the pattern-assignment rules of {@code javaRules.key}, which decompose assignments whose
 * initializer binds pattern variables:
 *
 * <ul>
 * <li>{@code instanceofPatternAssignmentSE/NSE}: {@code b = e instanceof T v;} loses the pattern
 * variable {@code v}</li>
 * <li>{@code andPatternAssignment}/{@code orPatternAssignment}: short-circuit decompositions that
 * declare the pattern variables of a binding guard in the branch where the guard is known to be
 * matched</li>
 * <li>{@code notPatternAssignment}: negated binding guard</li>
 * <li>{@code conditionalPatternAssignment}: ternary whose condition is a binding guard</li>
 * </ul>
 *
 * <p>
 * All six rules are loaded from the production rule file {@code javaRules.key} (no test-only
 * copies). Note that loading this file requires the jmlparser to support the
 * {@code #posBinding}/{@code #negBinding} program meta-constructs; until the parser supports
 * them, the rule base cannot be loaded and all tests of this class are skipped (see
 * {@link #setUp()}).
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
            if (hasCause(e, BuildingException.class)) {
                LOGGER.warn(
                    "Skipping pattern-assignment rule tests: javaRules.key cannot be loaded until"
                        + " the jmlparser supports the #posBinding/#negBinding meta-constructs."
                        + " Last error: {}",
                    e.getMessage());
                Assumptions.assumeTrue(false,
                    "javaRules.key cannot be loaded (" + e.getMessage()
                        + "); the pattern-assignment"
                        + " rule tests are skipped until the jmlparser supports the"
                        + " #posBinding/#negBinding meta-constructs.");
            }
            throw e instanceof RuntimeException re ? re : new RuntimeException(e);
        }
        services = initConfig.getServices();
        allRules = initConfig.createTacletIndex();
    }

    private static boolean hasCause(Throwable t, Class<? extends Throwable> type) {
        for (Throwable c = t; c != null; c = c.getCause()) {
            if (type.isInstance(c)) {
                return true;
            }
        }
        return false;
    }

    private JTerm parseTerm(String term) {
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
     * The pretty-printed succedent formula of the goal with all whitespace removed, so the
     * assertions below do not depend on the printer's line breaking and indentation.
     */
    private static String printed(Goal goal) {
        var formula = goal.sequent().succedent().getFirst().formula();
        return formula.toString().replaceAll("\\s+", "");
    }

    @Test
    void instanceofPatternAssignmentSE() {
        var goal = applyRule("instanceofPatternAssignmentSE",
            "Object o; boolean b = o instanceof String s;");
        assertEquals("\\<Objecto;booleanb=oinstanceofString;\\>true", printed(goal));
    }

    @Test
    void instanceofPatternAssignmentNSE() {
        var goal = applyRule("instanceofPatternAssignmentNSE",
            "Object o; boolean b = (o == null ? o : o) instanceof String s;");
        assertEquals("\\<Objecto;booleanb=(o==null?o:o)instanceofString;\\>true", printed(goal));
    }

    @Test
    void andPatternAssignment() {
        var goal = applyRule("andPatternAssignment",
            "Object o; boolean b = o instanceof String s && o == null;");
        // The guard is evaluated once into a fresh boolean variable b_1 (the name proposed for a
        // new boolean variable next to the existing variable b); the pattern variable s is
        // declared in the branch where the guard is known to have matched.
        assertEquals("\\<Objecto;booleanb;booleanb_1;{b_1=oinstanceofStrings;}"
            + "if(b_1){Strings=(String)o;b=o==null;}"
            + "else{b=false;}\\>true", printed(goal));
    }

    @Test
    void orPatternAssignment() {
        var goal = applyRule("orPatternAssignment",
            "Object o; boolean b = o instanceof String s || o == null;");
        assertEquals("\\<Objecto;booleanb;booleanb_1;{b_1=oinstanceofStrings;}"
            + "if(b_1){b=true;}"
            + "else{b=o==null;}\\>true", printed(goal));
    }

    @Test
    void notPatternAssignment() {
        var goal = applyRule("notPatternAssignment",
            "Object o; boolean b = !(o instanceof String s);");
        assertEquals("\\<Objecto;booleanb;booleanb_1;{b_1=!(oinstanceofStrings);}b=!b_1;\\>true",
            printed(goal));
    }

    @Test
    void conditionalPatternAssignment() {
        var goal = applyRule("conditionalPatternAssignment",
            "Object o; Object r = !(o instanceof String s) ? o : o;");
        // The negated guard binds s only when it evaluates to false, hence s is declared in the
        // else-branch. The fresh guard variable is named b, since no variable with this basename
        // occurs in the program.
        assertEquals("\\<Objecto;Objectr;booleanb;{b=!(oinstanceofStrings);}"
            + "if(b){r=o;}"
            + "else{Strings=(String)o;r=o;}\\>true", printed(goal));
    }
}

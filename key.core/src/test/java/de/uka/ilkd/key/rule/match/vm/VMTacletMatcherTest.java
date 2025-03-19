/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.match.vm;

import java.io.File;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.parser.ParserException;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.rule.FindTaclet;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.util.HelperClassForTests;

import org.key_project.logic.Name;

import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

public class VMTacletMatcherTest {

    private static final int NR_TACLETS = 6;

    private static Services services;
    private static final Taclet[] taclet = new Taclet[NR_TACLETS];
    private static final VMTacletMatcher[] matcher = new VMTacletMatcher[NR_TACLETS];

    static {// for JUnit 3
        init();
    }

    @BeforeAll
    public static void init() {
        HelperClassForTests helper = new HelperClassForTests();
        ProofAggregate pa = helper.parse(
            new File(HelperClassForTests.TESTCASE_DIRECTORY + "/tacletmatch/tacletMatch1.key"));

        for (int i = 0; i < NR_TACLETS; i++) {
            taclet[i] = pa.getFirstProof().getInitConfig()
                    .lookupActiveTaclet(new Name("taclet_match_rule_" + (i + 1)));
            assertNotNull(taclet[i], "Taclet required for test not found");
            assertTrue(taclet[i] instanceof FindTaclet,
                "Taclet should be a FindTaclet, but is not.");
            matcher[i] = new VMTacletMatcher(taclet[i]);
        }
        services = pa.getFirstProof().getServices();
    }

    @Test
    public void testMatchPropositionalFormula() throws ParserException {
        Term findTerm = ((FindTaclet) taclet[0]).find();

        final String[] matchingFormulas =
            { "A & B", "(!A | (A<->B)) & B", "A & (B & A)", "(\\forall int x; x>=0) & A" };

        for (String fml : matchingFormulas) {
            Term toMatch = services.getTermBuilder().parseTerm(fml);

            MatchConditions mc =
                matcher[0].matchFind(toMatch, MatchConditions.EMPTY_MATCHCONDITIONS, services);

            assertNotNull(mc,
                "Expected that " + findTerm + " matches " + toMatch + " but did not.");
            assertSame(mc.getInstantiations().lookupValue(new Name("phi")), toMatch.sub(0));
            assertSame(mc.getInstantiations().lookupValue(new Name("psi")), toMatch.sub(1));
        }


        final String[] notMatchingFormulas = { "A | (B & A)", "A", "\\forall int x;(x>=0 & A)" };
        for (String fml : notMatchingFormulas) {
            Term toMatch = services.getTermBuilder().parseTerm(fml);
            MatchConditions mc =
                matcher[0].matchFind(toMatch, MatchConditions.EMPTY_MATCHCONDITIONS, services);

            assertNull(mc,
                "Expected that " + findTerm + " does not match " + toMatch + " but it did.");
        }
    }

    @Test
    public void testMatchFunctionTerm() throws ParserException {

        Term findTerm = ((FindTaclet) taclet[1]).find();

        final String[] matchingFormulas = { "f(1, 1, 2)", "f(c, c, d)" };

        for (String fml : matchingFormulas) {
            Term toMatch = services.getTermBuilder().parseTerm(fml);

            MatchConditions mc =
                matcher[1].matchFind(toMatch, MatchConditions.EMPTY_MATCHCONDITIONS, services);

            assertNotNull(mc,
                "Expected that " + findTerm + " matches " + toMatch + " but did not.");
        }

        final String[] notMatchingFormulas = { "f(1,2,1)", "g(1,1,2)", "g(1,2,1)", "h(1,1)",
            "h(1,2)", "c", "z(1,1,1,1)", "f(c,d,c)" };
        for (String fml : notMatchingFormulas) {
            Term toMatch = services.getTermBuilder().parseTerm(fml);
            MatchConditions mc =
                matcher[1].matchFind(toMatch, MatchConditions.EMPTY_MATCHCONDITIONS, services);

            assertNull(mc,
                "Expected that " + findTerm + " does not match " + toMatch + " but it did.");
        }


    }

    @Test
    public void matchVarBindingTermSingle() throws ParserException {
        Term findTerm = ((FindTaclet) taclet[2]).find();

        Term toMatch = services.getTermBuilder().parseTerm("\\forall int x; x + 1 > 0");

        MatchConditions mc =
            matcher[2].matchFind(toMatch, MatchConditions.EMPTY_MATCHCONDITIONS, services);
        assertNotNull(mc, "Expected that " + findTerm + " matches " + toMatch + " but did not.");

        toMatch = services.getTermBuilder().parseTerm("\\forall int x; 1 + x > 0");

        mc = matcher[2].matchFind(toMatch, MatchConditions.EMPTY_MATCHCONDITIONS, services);
        assertNull(mc, "Expected that " + findTerm + " does not match " + toMatch + " but it did.");

    }

    @Test
    public void testMatchVarBindingTermNested() throws ParserException {
        Term findTerm = ((FindTaclet) taclet[3]).find();

        final String[] matchingFormulas = { "\\forall int x; \\forall int y; x + y > 0" };

        for (String fml : matchingFormulas) {
            Term toMatch = services.getTermBuilder().parseTerm(fml);

            MatchConditions mc =
                matcher[3].matchFind(toMatch, MatchConditions.EMPTY_MATCHCONDITIONS, services);

            assertNotNull(mc,
                "Expected that " + findTerm + " matches " + toMatch + " but did not.");
        }

        final String[] notMatchingFormulas = { "\\forall int x; \\forall int y; y + x > 0",
            "\\forall int x; \\forall int x; x + x > 0" };
        for (String fml : notMatchingFormulas) {
            Term toMatch = services.getTermBuilder().parseTerm(fml);
            MatchConditions mc =
                matcher[3].matchFind(toMatch, MatchConditions.EMPTY_MATCHCONDITIONS, services);

            assertNull(mc,
                "Expected that " + findTerm + " does not match " + toMatch + " but it did.");
        }

    }

    @Test
    public void testMatchVarBindingTermHiding() throws ParserException {
        Term findTerm = ((FindTaclet) taclet[4]).find();

        final String[] matchingFormulas = { "\\forall int x; (x > 0  & \\forall int y; x + y > 0)",
            "\\forall int x; (x > 0  & \\forall int x; x + x > 0)" };

        for (String fml : matchingFormulas) {
            Term toMatch = services.getTermBuilder().parseTerm(fml);

            MatchConditions mc =
                matcher[4].matchFind(toMatch, MatchConditions.EMPTY_MATCHCONDITIONS, services);

            assertNotNull(mc,
                "Expected that " + findTerm + " matches " + toMatch + " but did not.");
        }

        final String[] notMatchingFormulas =
            { "\\forall int x; (x > 0  & \\forall int y; y + x > 0)", };
        for (String fml : notMatchingFormulas) {
            Term toMatch = services.getTermBuilder().parseTerm(fml);
            MatchConditions mc =
                matcher[4].matchFind(toMatch, MatchConditions.EMPTY_MATCHCONDITIONS, services);

            assertNull(mc,
                "Expected that " + findTerm + " does not match " + toMatch + " but it did.");
        }

    }

    @Test
    public void testMatchVarBindingTermMoreHiding() throws ParserException {
        Term findTerm = ((FindTaclet) taclet[5]).find();

        final String[] matchingFormulas =
            { "\\forall int x; (x > 0  & \\forall int y; x + y > 0)" };

        for (String fml : matchingFormulas) {
            Term toMatch = services.getTermBuilder().parseTerm(fml);

            MatchConditions mc =
                matcher[5].matchFind(toMatch, MatchConditions.EMPTY_MATCHCONDITIONS, services);

            assertNotNull(mc,
                "Expected that " + findTerm + " matches " + toMatch + " but did not.");
        }

        final String[] notMatchingFormulas =
            { "\\forall int x; (x > 0  & \\forall int x; x + x > 0)",
                "\\forall int x; (x > 0  & \\forall int y; y + x > 0)", };
        for (String fml : notMatchingFormulas) {
            Term toMatch = services.getTermBuilder().parseTerm(fml);
            MatchConditions mc =
                matcher[5].matchFind(toMatch, MatchConditions.EMPTY_MATCHCONDITIONS, services);

            assertNull(mc,
                "Expected that " + findTerm + " does not match " + toMatch + " but it did.");
        }
    }

}

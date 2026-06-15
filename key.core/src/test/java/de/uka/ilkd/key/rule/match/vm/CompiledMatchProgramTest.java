/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.match.vm;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.parser.ParserException;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.rule.FindTaclet;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.util.HelperClassForTests;

import org.key_project.logic.Name;
import org.key_project.prover.rules.instantiation.MatchResultInfo;
import org.key_project.prover.rules.matcher.vm.MatchProgram;

import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Unit tests for the cursor-free compiled find-matcher built by the match-plan framework
 * ({@link JavaMatchPlanBuilder#compiledProgram}), the compiled counterpart of
 * {@link VMTacletMatcherTest} (which covers the interpreter). For the same taclets and the same
 * matching / non-matching terms it asserts that the compiled matcher produces the expected result
 * -- success with the expected schema-variable instantiations, and {@code null} on the failure
 * cases -- so the compiled path is checked against explicit expectations.
 *
 * <p>
 * Coverage focuses on term-level matching (propositional / function patterns) and, importantly,
 * {@link #compiledBoundVariableMatching() bound variables} (quantifiers / renaming), which the
 * compiler handles cursor-free.
 */
public class CompiledMatchProgramTest {

    private static final MatchResultInfo EMPTY = MatchConditions.EMPTY_MATCHCONDITIONS;

    private static Services services;
    private static FindTaclet propositional; // taclet_match_rule_1: phi & psi
    private static FindTaclet function; // taclet_match_rule_2: f(...)
    private static FindTaclet binder; // taclet_match_rule_3: \forall x; ...

    @BeforeAll
    public static void init() {
        final ProofAggregate pa = HelperClassForTests.parse(
            HelperClassForTests.TESTCASE_DIRECTORY.resolve("tacletmatch")
                    .resolve("tacletMatch1.key"));
        services = pa.getFirstProof().getServices();
        propositional = findTaclet(pa, "taclet_match_rule_1");
        function = findTaclet(pa, "taclet_match_rule_2");
        binder = findTaclet(pa, "taclet_match_rule_3");
    }

    private static FindTaclet findTaclet(ProofAggregate pa, String name) {
        final Taclet t =
            pa.getFirstProof().getInitConfig().lookupActiveTaclet(new Name(name));
        assertTrue(t instanceof FindTaclet, name + " must be a find taclet");
        return (FindTaclet) t;
    }

    /** compiles the find expression; the taclets here are all within the framework's coverage. */
    private static MatchProgram compile(FindTaclet t) {
        final MatchProgram p = JavaMatchPlanBuilder.compiledProgram((JTerm) t.find());
        assertNotNull(p, "find pattern of " + t.name() + " was expected to compile");
        return p;
    }

    private MatchResultInfo match(MatchProgram p, String term) throws ParserException {
        return p.match(services.getTermBuilder().parseTerm(term), EMPTY, services);
    }

    @Test
    public void compiledPropositionalMatching() throws ParserException {
        final MatchProgram p = compile(propositional);

        final JTerm toMatch = services.getTermBuilder().parseTerm("A & B");
        final MatchResultInfo mc = p.match(toMatch, EMPTY, services);
        assertNotNull(mc, "compiled matcher should match A & B");
        assertSame(toMatch.sub(0), mc.getInstantiations().lookupValue(new Name("phi")));
        assertSame(toMatch.sub(1), mc.getInstantiations().lookupValue(new Name("psi")));

        for (String matching : new String[] { "(!A | (A<->B)) & B", "A & (B & A)",
            "(\\forall int x; x>=0) & A" }) {
            assertNotNull(match(p, matching), "compiled matcher should match " + matching);
        }
        // failure cases
        for (String nonMatching : new String[] { "A | (B & A)", "A",
            "\\forall int x;(x>=0 & A)" }) {
            assertNull(match(p, nonMatching), "compiled matcher should not match " + nonMatching);
        }
    }

    @Test
    public void compiledFunctionMatching() throws ParserException {
        final MatchProgram p = compile(function);

        for (String matching : new String[] { "f(1, 1, 2)", "f(c, c, d)" }) {
            assertNotNull(match(p, matching), "compiled matcher should match " + matching);
        }
        // failure cases: wrong shape / different head symbol / repeated-SV mismatch
        for (String nonMatching : new String[] { "f(1,2,1)", "g(1,1,2)", "h(1,1)", "c",
            "z(1,1,1,1)", "f(c,d,c)" }) {
            assertNull(match(p, nonMatching), "compiled matcher should not match " + nonMatching);
        }
    }

    @Test
    public void compiledBoundVariableMatching() throws ParserException {
        final MatchProgram p = compile(binder);

        assertNotNull(match(p, "\\forall int x; x + 1 > 0"),
            "compiled matcher should match the bound-variable pattern");
        // failure case: the body shape differs (1 + x rather than x + 1)
        assertNull(match(p, "\\forall int x; 1 + x > 0"),
            "compiled matcher should not match a differing bound-variable body");
    }
}

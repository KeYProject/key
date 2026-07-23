/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.quantifierHeuristics;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.JFunction;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.sort.SortImpl;
import de.uka.ilkd.key.rule.TacletForTests;
import de.uka.ilkd.key.strategy.quantifierHeuristics.PolarityOccurrenceTieBreak.OccInfo;

import org.key_project.logic.Name;
import org.key_project.logic.op.Function;
import org.key_project.logic.sort.Sort;
import org.key_project.prover.sequent.SequentFormula;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Checks the polarity walk behind the occurrence tie-break: which operators of a sequent formula
 * are recorded at proving polarity {@code +1} respectively {@code -1}, relative to the formula
 * root. Negation and the left of an implication flip, conjunction, disjunction and the right of
 * an implication keep, quantifiers and equivalences are neutral, the condition of a conditional
 * is neutral while its branches keep, and below an atom the polarity is frozen for the atom's
 * whole subtree.
 */
public class PolarityWalkTest {

    private static final Services SERVICES = TacletForTests.services();
    private static final TermBuilder TB = SERVICES.getTermBuilder();

    private static final Sort S = new SortImpl(new Name("polS"));
    private static final Function A = new JFunction(new Name("polA"), S);
    private static final Function G = new JFunction(new Name("polG"), S, S);
    private static final Function P = pred("polP");
    private static final Function Q = pred("polQ");

    private static JFunction pred(String name) {
        return new JFunction(new Name(name), de.uka.ilkd.key.ldt.JavaDLTheory.FORMULA, S);
    }

    private static JTerm p() {
        return TB.func(P, TB.func(G, TB.func(A)));
    }

    private static JTerm q() {
        return TB.func(Q, TB.func(A));
    }

    private static OccInfo walk(JTerm formula) {
        return PolarityOccurrenceTieBreak.occInfo(new SequentFormula(formula), SERVICES);
    }

    private static void assertPlus(OccInfo info, Function op) {
        assertTrue(info.opsRelPlus().contains(op), op + " must be at proving polarity +1");
        assertFalse(info.opsRelMinus().contains(op), op + " must not also be at -1");
    }

    private static void assertMinus(OccInfo info, Function op) {
        assertTrue(info.opsRelMinus().contains(op), op + " must be at proving polarity -1");
        assertFalse(info.opsRelPlus().contains(op), op + " must not also be at +1");
    }

    private static void assertNeutral(OccInfo info, Function op) {
        assertTrue(info.opsAny().contains(op), op + " must be seen by the walk");
        assertFalse(info.opsRelPlus().contains(op) || info.opsRelMinus().contains(op),
            op + " must be at neutral polarity");
    }

    @Test
    void conjunctionAndDisjunctionKeepThePolarity() {
        final OccInfo and = walk(TB.and(p(), q()));
        assertPlus(and, P);
        assertPlus(and, Q);
        final OccInfo or = walk(TB.or(p(), q()));
        assertPlus(or, P);
        assertPlus(or, Q);
    }

    @Test
    void negationFlipsThePolarity() {
        final OccInfo info = walk(TB.not(p()));
        assertMinus(info, P);
        final OccInfo doubled = walk(TB.not(TB.not(p())));
        assertPlus(doubled, P);
    }

    @Test
    void implicationFlipsOnlyItsLeft() {
        final OccInfo info = walk(TB.imp(p(), q()));
        assertMinus(info, P);
        assertPlus(info, Q);
    }

    @Test
    void quantifierAndEquivalenceAreNeutral() {
        final LogicVariable x = new LogicVariable(new Name("polX"), S);
        final OccInfo all = walk(TB.all(x, TB.func(P, TB.var(x))));
        assertNeutral(all, P);
        final OccInfo eqv = walk(
            SERVICES.getTermFactory().createTerm(
                de.uka.ilkd.key.logic.op.Equality.EQV, p(), q()));
        assertNeutral(eqv, P);
        assertNeutral(eqv, Q);
    }

    @Test
    void conditionIsNeutralWhileBranchesKeep() {
        final OccInfo info = walk(TB.ife(p(), q(), q()));
        assertNeutral(info, P);
        assertPlus(info, Q);
    }

    @Test
    void polarityIsFrozenBelowAnAtom() {
        // P itself is the atom of the formula !P(g(a)): the atom is at -1, and so is its whole
        // subtree, the function g and the constant a included.
        final OccInfo info = walk(TB.not(p()));
        assertMinus(info, P);
        assertMinus(info, G);
        assertMinus(info, A);
    }
}

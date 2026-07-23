/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.quantifierHeuristics;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.JFunction;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.rule.TacletForTests;

import org.key_project.logic.Name;
import org.key_project.logic.op.Function;
import org.key_project.logic.sort.Sort;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Tests for the arithmetic reasoning used to judge quantifier instantiations
 * ({@link HandleArith}). The quantifier heuristic scores an instantiation as useless when the
 * instantiated formula is trivially true given the assumptions; deciding that relies on being
 * able to prove one integer comparison from another. These tests pin that reasoning.
 */
public class HandleArithTest {

    private Services services;
    private TermBuilder tb;
    /** an integer constant standing for a skolem index like {@code j_3}. */
    private JTerm c;

    @BeforeEach
    public void setUp() {
        services = TacletForTests.services();
        tb = services.getTermBuilder();
        final Sort intSort = services.getTypeConverter().getIntegerLDT().targetSort();
        final Function cf = new JFunction(new Name("c_idx"), intSort);
        c = tb.func(cf);
    }

    /** Whether {@link HandleArith#provedByArith} proves {@code problem} from {@code axiom}. */
    private boolean provesTrue(JTerm problem, JTerm axiom) {
        return HandleArith.provedByArith(problem, axiom, services).op() == Junctor.TRUE;
    }

    /** Whether {@code problem} is refuted (its negation proved) from {@code axiom}. */
    private boolean provesFalse(JTerm problem, JTerm axiom) {
        return HandleArith.provedByArith(problem, axiom, services).op() == Junctor.FALSE;
    }

    @Test
    public void deduceLessThanZeroFromAtMostMinusOne() {
        // c <= -1 entails c < 0 (over the integers c < 0 is c <= -1)
        assertEquals(true, provesTrue(tb.lt(c, tb.zero()), tb.leq(c, tb.zTerm(-1))));
    }

    @Test
    public void deduceAtMostMinusOneFromLessThanZero() {
        // c < 0 entails c <= -1 (the strict-assumption direction)
        assertEquals(true, provesTrue(tb.leq(c, tb.zTerm(-1)), tb.lt(c, tb.zero())));
    }

    @Test
    public void anAxiomProvesItself() {
        // the range literal is literally an assumption
        assertEquals(true, provesTrue(tb.leq(c, tb.zTerm(-1)), tb.leq(c, tb.zTerm(-1))));
    }

    @Test
    public void weakerUpperBoundFollows() {
        // c <= -1 entails c <= 5
        assertEquals(true, provesTrue(tb.leq(c, tb.zTerm(5)), tb.leq(c, tb.zTerm(-1))));
    }

    @Test
    public void strongerLowerBoundEntailsWeakerOne() {
        // c <= -2 entails c <= -1
        assertEquals(true, provesTrue(tb.leq(c, tb.zTerm(-1)), tb.leq(c, tb.zTerm(-2))));
    }

    @Test
    public void contradictoryLowerBoundIsRefuted() {
        // c <= -1 makes c >= 0 false
        assertEquals(true, provesFalse(tb.geq(c, tb.zero()), tb.leq(c, tb.zTerm(-1))));
    }

    @Test
    public void unrelatedBoundProvesNothing() {
        // c <= 5 neither proves nor refutes c <= -1
        final JTerm r = HandleArith.provedByArith(tb.leq(c, tb.zTerm(-1)), tb.leq(c, tb.zTerm(5)),
            services);
        assertEquals(false, r.op() == Junctor.TRUE || r.op() == Junctor.FALSE);
    }
}

/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.quantifierHeuristics;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.JFunction;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.rule.TacletForTests;

import org.key_project.logic.Name;
import org.key_project.logic.Term;
import org.key_project.logic.op.Function;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.logic.sort.Sort;
import org.key_project.util.collection.DefaultImmutableMap;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableMap;
import org.key_project.util.collection.ImmutableSet;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;

/**
 * Tests for the cost the quantifier heuristic assigns to a candidate instantiation
 * ({@link PredictCostProver#computerInstanceCost}). A cost of {@code -1} means the instantiated
 * formula is trivially true under the assumptions, so the instantiation is useless and is
 * dropped by the callers.
 *
 * <p>
 * The formula modelled here is an array range invariant of the shape occurring in removeDup:
 * {@code x <= -1 | x >= n | p(x)} (index out of range below, out of range above, or the element
 * property holds). Instantiating it with an index known to be out of range makes a range
 * disjunct true, so the instance is useless and its cost must be {@code -1}.
 */
public class PredictCostProverTest {

    private Services services;
    private TermBuilder tb;
    private LogicVariable x; // the quantified index
    private JTerm c; // the concrete index to instantiate with (a skolem like j_3)
    private JTerm n; // the upper range bound
    private Function p; // the element property p(int) : Formula

    @BeforeEach
    public void setUp() {
        services = TacletForTests.services();
        tb = services.getTermBuilder();
        final Sort intSort = services.getTypeConverter().getIntegerLDT().targetSort();
        x = new LogicVariable(new Name("x"), intSort);
        c = tb.func(new JFunction(new Name("c_idx"), intSort));
        n = tb.func(new JFunction(new Name("n_bound"), intSort));
        p = new JFunction(new Name("p_prop"), JavaDLTheory.FORMULA, intSort);
    }

    /** The invariant body {@code x <= -1 | x >= n | p(x)}. */
    private JTerm matrix() {
        return tb.or(tb.leq(tb.var(x), tb.zTerm(-1)),
            tb.or(tb.geq(tb.var(x), n), tb.func(p, tb.var(x))));
    }

    /** The substitution {@code x := c}. */
    private Substitution instantiateWithC() {
        ImmutableMap<QuantifiableVariable, Term> map = DefaultImmutableMap.nilMap();
        map = map.put(x, c);
        return new Substitution(map);
    }

    private ImmutableSet<JTerm> assumptions(JTerm... literals) {
        ImmutableSet<JTerm> set = DefaultImmutableSet.nil();
        for (JTerm literal : literals) {
            set = set.add(literal);
        }
        return set;
    }

    private long cost(ImmutableSet<JTerm> assumptions) {
        return PredictCostProver.computerInstanceCost(instantiateWithC(), matrix(), assumptions,
            services);
    }

    @Test
    public void uselessWhenLowerBoundKnownDirectly() {
        // c <= -1 is assumed, so the first disjunct is true and the instance is useless
        assertEquals(-1, cost(assumptions(tb.leq(c, tb.zTerm(-1)))));
    }

    @Test
    public void uselessWhenStrongerLowerBoundKnown() {
        // c <= -2 entails c <= -1, so the first disjunct is still provably true
        assertEquals(-1, cost(assumptions(tb.leq(c, tb.zTerm(-2)))));
    }

    @Test
    public void uselessWhenUpperBoundKnown() {
        // c >= n is assumed, so the second disjunct is true
        assertEquals(-1, cost(assumptions(tb.geq(c, n))));
    }

    @Test
    public void usefulWhenIndexInRange() {
        // 0 <= c < n leaves only p(c): the instance is not trivially true
        assertNotEquals(-1, cost(assumptions(tb.geq(c, tb.zero()), tb.lt(c, n))));
    }

    @Test
    public void usefulWhenNothingKnown() {
        // without any range assumption the element property remains, so not useless
        assertNotEquals(-1, cost(assumptions()));
    }
}

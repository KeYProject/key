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

import org.key_project.logic.Name;
import org.key_project.logic.op.Function;
import org.key_project.logic.sort.Sort;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableSet;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Checks {@link Congruence}: an assumed equality rewrites occurrences of its left side to its
 * right side, the direction flips when the sequent's orientation would widen the sort, number
 * literals end up as the representative of their class, and terms binding variables are left
 * untouched. These are the properties the prediction relies on when it normalizes literals
 * before deciding them.
 */
public class CongruenceTest {

    private static final Services SERVICES = TacletForTests.services();
    private static final TermBuilder TB = SERVICES.getTermBuilder();

    private static ImmutableSet<JTerm> literals(JTerm... lits) {
        ImmutableSet<JTerm> set = DefaultImmutableSet.nil();
        for (final JTerm lit : lits) {
            set = set.add(lit);
        }
        return set;
    }

    @Test
    void rewritesAlongTheSequentOrientation() {
        final Sort s = new SortImpl(new Name("congS"));
        final Function a = new JFunction(new Name("congA"), s);
        final Function b = new JFunction(new Name("congB"), s);
        final Function f = new JFunction(new Name("congF"), s, s);
        final JTerm ta = TB.func(a);
        final JTerm tb = TB.func(b);

        final Congruence c = new Congruence(literals(TB.equals(ta, tb)), SERVICES);
        assertFalse(c.isTrivial());
        assertEquals(tb, c.normalize(ta), "the left side rewrites to the right side");
        assertEquals(TB.func(f, tb), c.normalize(TB.func(f, ta)),
            "occurrences below an operator rewrite as well");
        assertEquals(tb, c.normalize(tb), "the representative stays itself");
    }

    @Test
    void wideningDirectionIsFlipped() {
        final Sort wide = new SortImpl(new Name("congWide"));
        final Sort narrow = new SortImpl(new Name("congNarrow"), wide);
        final Function o = new JFunction(new Name("congO"), wide);
        final Function d = new JFunction(new Name("congD"), narrow);
        final JTerm to = TB.func(o);
        final JTerm td = TB.func(d);

        // Written with the narrow term on the left: reading it left to right would put the
        // wide-sorted term into positions requiring the narrow sort, so the direction flips.
        final Congruence c = new Congruence(literals(TB.equals(td, to)), SERVICES);
        assertEquals(td, c.normalize(to),
            "the wide term rewrites to the narrow one, not the other way around");
        assertEquals(td, c.normalize(td));

        // Written with the wide term on the left, the sequent orientation is already narrowing.
        final Congruence c2 = new Congruence(literals(TB.equals(to, td)), SERVICES);
        assertEquals(td, c2.normalize(to));
    }

    @Test
    void numberLiteralsBecomeTheRepresentative() {
        final Sort intSort = SERVICES.getTypeConverter().getIntegerLDT().targetSort();
        final Function a = new JFunction(new Name("congIntA"), intSort);
        final JTerm ta = TB.func(a);
        final JTerm five = TB.zTerm(5);

        final Congruence left = new Congruence(literals(TB.equals(ta, five)), SERVICES);
        assertEquals(five, left.normalize(ta), "a = 5 rewrites a to 5");
        final Congruence right = new Congruence(literals(TB.equals(five, ta)), SERVICES);
        assertEquals(five, right.normalize(ta),
            "5 = a also rewrites a to 5: the theory refuses a literal that rewrites away");
    }

    @Test
    void termsBindingVariablesAreLeftUntouched() {
        final Sort s = new SortImpl(new Name("congBindS"));
        final Function a = new JFunction(new Name("congBindA"), s);
        final Function b = new JFunction(new Name("congBindB"), s);
        final Function p =
            new JFunction(new Name("congBindP"), de.uka.ilkd.key.ldt.JavaDLTheory.FORMULA, s);
        final LogicVariable x = new LogicVariable(new Name("congBindX"), s);

        final Congruence c =
            new Congruence(literals(TB.equals(TB.func(a), TB.func(b))), SERVICES);
        final JTerm quantified = TB.all(x, TB.func(p, TB.func(a)));
        assertSame(quantified, c.normalize(quantified),
            "a term binding variables is returned as it is");
    }

    @Test
    void trivialWithoutEqualities() {
        final Congruence c = new Congruence(DefaultImmutableSet.nil(), SERVICES);
        assertTrue(c.isTrivial());
        final JTerm t = TB.tt();
        assertSame(t, c.normalize(t), "the trivial congruence is the identity");
    }
}

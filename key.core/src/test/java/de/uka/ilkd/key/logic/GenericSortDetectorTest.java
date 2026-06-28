/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic;

import java.util.List;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.logic.op.JFunction;
import de.uka.ilkd.key.logic.sort.GenericSort;
import de.uka.ilkd.key.logic.sort.ParametricSortDecl;
import de.uka.ilkd.key.logic.sort.ParametricSortInstance;
import de.uka.ilkd.key.rule.TacletForTests;

import org.key_project.logic.Name;
import org.key_project.logic.sort.Sort;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Unit tests for {@link GenericSortDetector}, the shared checker used at the parser/user-input
 * boundaries to reject generic sorts leaking into concrete terms (issue #3409).
 */
class GenericSortDetectorTest {

    @Test
    void detectsConstantOfGenericSort() {
        Services services = TacletForTests.services().copy(false);
        GenericSort s = new GenericSort(new Name("S"));
        JFunction c = new JFunction(new Name("c"), s);
        JTerm t = services.getTermBuilder().func(c);

        assertEquals(List.of(s), GenericSortDetector.findIn(t),
            "a constant of generic sort must be detected");
    }

    @Test
    void detectsGenericSortNestedInArgument() {
        Services services = TacletForTests.services().copy(false);
        var tb = services.getTermBuilder();
        GenericSort s = new GenericSort(new Name("S"));
        JFunction c = new JFunction(new Name("c"), s);
        // p(c) with p : (S) -> Formula -- generic only appears in the argument's sort
        JFunction p = new JFunction(new Name("p"), JavaDLTheory.FORMULA, s);
        JTerm t = tb.func(p, tb.func(c));

        assertEquals(List.of(s), GenericSortDetector.findIn(t),
            "a generic sort nested in a subterm must be detected");
    }

    /**
     * The case that a plain {@code instanceof GenericSort} check would miss: a sort that is not
     * itself a generic sort but <em>contains</em> one, like {@code List<[G1]>} (the same situation
     * arises for {@code select<[E]>(...)}). Detection must rely on
     * {@link Sort#containsGenericSort()}.
     */
    @Test
    void detectsGenericSortNestedInParametricSort() {
        Services services = TacletForTests.services().copy(false);
        var tb = services.getTermBuilder();

        GenericSort g1 = new GenericSort(new Name("G1"));
        services.getNamespaces().sorts().add(g1);
        ParametricSortDecl listDecl = new ParametricSortDecl(new Name("List"), false,
            ImmutableSet.empty(),
            ImmutableList.of(new GenericParameter(g1, GenericParameter.Variance.INVARIANT)));
        services.getNamespaces().parametricSorts().add(listDecl);
        Sort listOfG1 = ParametricSortInstance.get(listDecl,
            ImmutableList.of(new GenericArgument(g1)), services);

        JFunction c = new JFunction(new Name("c"), listOfG1);
        JTerm t = tb.func(c);

        List<Sort> found = GenericSortDetector.findIn(t);
        assertEquals(List.of(listOfG1), found,
            "a generic sort nested in a parametric sort (List<[G1]>) must be detected, even "
                + "though the term's sort is not itself a GenericSort");
        assertTrue(found.get(0).containsGenericSort());
        assertFalse(found.get(0) instanceof GenericSort,
            "the reported sort is the containing parametric sort, not a bare GenericSort");
    }

    @Test
    void reportsAllDistinctGenericSorts() {
        Services services = TacletForTests.services().copy(false);
        var tb = services.getTermBuilder();
        GenericSort s = new GenericSort(new Name("S"));
        GenericSort u = new GenericSort(new Name("U"));
        JFunction p = new JFunction(new Name("p"), JavaDLTheory.FORMULA, s);
        JFunction q = new JFunction(new Name("q"), JavaDLTheory.FORMULA, u);
        // p(cs) & q(cu) with cs : S, cu : U
        JTerm t = tb.and(tb.func(p, tb.func(new JFunction(new Name("cs"), s))),
            tb.func(q, tb.func(new JFunction(new Name("cu"), u))));

        assertEquals(List.of(s, u), GenericSortDetector.findIn(t),
            "all distinct generic sorts must be reported, in order of first occurrence");
    }

    @Test
    void concreteTermHasNoGenericSort() {
        Services services = TacletForTests.services().copy(false);
        var tb = services.getTermBuilder();
        Sort intSort = services.getNamespaces().sorts().lookup(new Name("int"));
        JFunction g = new JFunction(new Name("myConcreteConst"), intSort);
        JTerm t = tb.equals(tb.func(g), tb.func(g));

        assertTrue(GenericSortDetector.findIn(t).isEmpty(),
            "a fully concrete term must not be flagged");
    }
}

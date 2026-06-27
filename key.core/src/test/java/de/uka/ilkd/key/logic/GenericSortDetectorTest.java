/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.logic.op.JFunction;
import de.uka.ilkd.key.logic.sort.GenericSort;
import de.uka.ilkd.key.rule.TacletForTests;

import org.key_project.logic.Name;
import org.key_project.logic.sort.Sort;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;

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

        assertEquals(s, GenericSortDetector.findIn(t),
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

        assertEquals(s, GenericSortDetector.findIn(t),
            "a generic sort nested in a subterm must be detected");
    }

    @Test
    void concreteTermHasNoGenericSort() {
        Services services = TacletForTests.services().copy(false);
        var tb = services.getTermBuilder();
        Sort intSort = services.getNamespaces().sorts().lookup(new Name("int"));
        JFunction g = new JFunction(new Name("myConcreteConst"), intSort);
        JTerm t = tb.equals(tb.func(g), tb.func(g));

        assertNull(GenericSortDetector.findIn(t),
            "a fully concrete term must not be flagged");
    }
}

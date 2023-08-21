/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.merge;

import java.io.File;
import java.util.ArrayList;
import java.util.Iterator;

import de.uka.ilkd.key.axiom_abstraction.AbstractDomainElement;
import de.uka.ilkd.key.axiom_abstraction.predicateabstraction.AbstractionPredicate;
import de.uka.ilkd.key.axiom_abstraction.predicateabstraction.ConjunctivePredicateAbstractionDomainElement;
import de.uka.ilkd.key.axiom_abstraction.predicateabstraction.ConjunctivePredicateAbstractionLattice;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.util.HelperClassForTests;

import org.key_project.util.collection.DefaultImmutableSet;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Test suite for the predicates lattice implementation.
 *
 * @author Dominic Scheurer
 */
public class PredicateAbstractionLatticeTests {

    private static final File TEST_RESOURCES_DIR_PREFIX =
        new File(HelperClassForTests.TESTCASE_DIRECTORY, "merge/");

    @Test
    public void testCreateSignLatticeWithPredicates() {
        // Dummy proof to get a term builder.
        final Proof p = MergeRuleTests.loadProof(TEST_RESOURCES_DIR_PREFIX, "dummy.key");
        final Services services = p.getServices();

        final Sort intSort = p.getServices().getNamespaces().sorts().lookup("int");
        final TermBuilder tb = p.getServices().getTermBuilder();

        final AbstractionPredicate gtZero = AbstractionPredicate.create(intSort,
            (Term input) -> (tb.gt(input, tb.zero())), services);
        final AbstractionPredicate eqZero = AbstractionPredicate.create(intSort,
            (Term input) -> (tb.equals(input, tb.zero())), services);
        final AbstractionPredicate ltZero = AbstractionPredicate.create(intSort,
            (Term input) -> (tb.lt(input, tb.zero())), services);

        ArrayList<AbstractionPredicate> predicates = new ArrayList<>();

        predicates.add(gtZero);
        predicates.add(eqZero);
        predicates.add(ltZero);

        ConjunctivePredicateAbstractionLattice lattice =
            new ConjunctivePredicateAbstractionLattice(predicates);

        assertEquals(9, lattice.size());

        Iterator<AbstractDomainElement> it = lattice.iterator();

        ConjunctivePredicateAbstractionDomainElement e1, e2, e3, e4, e5, e6, e7, e8, e9;

        // BOTTOM
        assertEquals(e1 = ConjunctivePredicateAbstractionDomainElement.BOTTOM, it.next());
        // <0 & =0 & >0
        assertEquals(e2 = new ConjunctivePredicateAbstractionDomainElement(
            DefaultImmutableSet.<AbstractionPredicate>nil().add(ltZero).add(eqZero).add(gtZero)),
            it.next());
        // =0 & >0
        assertEquals(
            e3 = new ConjunctivePredicateAbstractionDomainElement(
                DefaultImmutableSet.<AbstractionPredicate>nil().add(eqZero).add(gtZero)),
            it.next());
        // <0 & >0
        assertEquals(
            e4 = new ConjunctivePredicateAbstractionDomainElement(
                DefaultImmutableSet.<AbstractionPredicate>nil().add(ltZero).add(gtZero)),
            it.next());
        // <0 & =0
        assertEquals(
            e5 = new ConjunctivePredicateAbstractionDomainElement(
                DefaultImmutableSet.<AbstractionPredicate>nil().add(ltZero).add(eqZero)),
            it.next());
        // >0
        assertEquals(e6 = new ConjunctivePredicateAbstractionDomainElement(
            DefaultImmutableSet.<AbstractionPredicate>nil().add(gtZero)), it.next());
        // =0
        assertEquals(e7 = new ConjunctivePredicateAbstractionDomainElement(
            DefaultImmutableSet.<AbstractionPredicate>nil().add(eqZero)), it.next());
        // <0
        assertEquals(e8 = new ConjunctivePredicateAbstractionDomainElement(
            DefaultImmutableSet.<AbstractionPredicate>nil().add(ltZero)), it.next());
        // TOP
        assertEquals(e9 = ConjunctivePredicateAbstractionDomainElement.TOP, it.next());

        // There should be no further elements.
        Assertions.assertFalse(it.hasNext());

        // Now try a few joins.
        // Joins with top should result in top.
        assertEquals(e9, lattice.join(e9, e4));
        assertEquals(e9, lattice.join(e9, e5));

        // Joins with bottom should result in the respective other element.
        assertEquals(e3, lattice.join(e1, e3));
        assertEquals(e2, lattice.join(e1, e2));
        assertEquals(e1, lattice.join(e1, e1));

        // (_<0)&(_=0) and (_=0)&(_>0) should result in (_=0)
        assertEquals(e7, lattice.join(e5, e3));

        // (_<0)&(_=0) and (_=0) should result in (_=0)
        assertEquals(e7, lattice.join(e5, e7));

        // <0 & =0 & >0 and =0 & >0 should result in =0 & >0
        assertEquals(e3, lattice.join(e2, e3));

        // <0 and >0 should result in TOP
        assertEquals(e9, lattice.join(e6, e8));
    }

    @Test
    public void testTrivialPredicatesLattice() {
        ArrayList<AbstractionPredicate> predicates = new ArrayList<>();

        ConjunctivePredicateAbstractionLattice lattice =
            new ConjunctivePredicateAbstractionLattice(predicates);

        assertEquals(2, lattice.size());

        Iterator<AbstractDomainElement> it = lattice.iterator();

        // BOTTOM
        assertEquals(ConjunctivePredicateAbstractionDomainElement.BOTTOM, it.next());
        // TOP
        assertEquals(ConjunctivePredicateAbstractionDomainElement.TOP, it.next());

        // This should be all.
        Assertions.assertFalse(it.hasNext());
    }

    @Test
    public void testToAndFromString() {
        // Dummy proof to get services etc.
        final Proof p = MergeRuleTests.loadProof(TEST_RESOURCES_DIR_PREFIX, "dummy.key");
        final Services services = p.getServices();
        final TermBuilder tb = services.getTermBuilder();

        final LocationVariable ph = new LocationVariable(new ProgramElementName("ph"),
            services.getNamespaces().sorts().lookup("int"));
        final AbstractionPredicate pred =
            AbstractionPredicate.create(tb.geq(tb.var(ph), tb.zero()), ph, services);
        final ArrayList<AbstractionPredicate> preds = new ArrayList<>();
        preds.add(pred);

        final ConjunctivePredicateAbstractionLattice lattice =
            new ConjunctivePredicateAbstractionLattice(preds);

        final Iterator<AbstractDomainElement> it = lattice.iterator();
        it.next(); // Skip bottom elem

        final AbstractDomainElement elem = it.next();

        assertEquals(elem, lattice.fromString(elem.toParseableString(services), services));
    }
}

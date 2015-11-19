// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2015 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.rule.join;

import java.util.ArrayList;
import java.util.Iterator;

import junit.framework.TestCase;

import org.junit.Test;
import org.key_project.util.collection.DefaultImmutableSet;

import de.uka.ilkd.key.axiom_abstraction.AbstractDomainElement;
import de.uka.ilkd.key.axiom_abstraction.AbstractionPredicate;
import de.uka.ilkd.key.axiom_abstraction.predicateabstraction.PredicateAbstractionDomainElement;
import de.uka.ilkd.key.axiom_abstraction.predicateabstraction.PredicateAbstractionLattice;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.proof.Proof;

/**
 * Test suite for the predicates lattice implementation.
 *
 * @author Dominic Scheurer
 */
public class PredicateAbstractionLatticeTests extends TestCase {

    @Test
    public void testCreateSignLatticeWithPredicates() {
        // Dummy proof to get a term builder.
        final Proof p = JoinRuleTests.loadProof("dummy.key");
        final TermBuilder tb = p.getServices().getTermBuilder();

        final AbstractionPredicate gtZero = gtZero(tb);
        final AbstractionPredicate eqZero = eqZero(tb);
        final AbstractionPredicate ltZero = ltZero(tb);

        ArrayList<AbstractionPredicate> predicates =
                new ArrayList<AbstractionPredicate>();

        predicates.add(gtZero);
        predicates.add(eqZero);
        predicates.add(ltZero);

        PredicateAbstractionLattice lattice =
                new PredicateAbstractionLattice(predicates);

        assertEquals(9, lattice.size());

        Iterator<AbstractDomainElement> it = lattice.iterator();

        PredicateAbstractionDomainElement e1, e2, e3, e4, e5, e6, e7, e8, e9;

        // BOTTOM
        assertEquals(e1 = PredicateAbstractionDomainElement.BOTTOM, it.next());
        // <0 & =0 & >0
        assertEquals(e2 =
                new PredicateAbstractionDomainElement(DefaultImmutableSet
                        .<AbstractionPredicate> nil().add(ltZero).add(eqZero)
                        .add(gtZero)), it.next());
        // =0 & >0
        assertEquals(e3 =
                new PredicateAbstractionDomainElement(DefaultImmutableSet
                        .<AbstractionPredicate> nil().add(eqZero).add(gtZero)),
                it.next());
        // <0 & >0
        assertEquals(e4 =
                new PredicateAbstractionDomainElement(DefaultImmutableSet
                        .<AbstractionPredicate> nil().add(ltZero).add(gtZero)),
                it.next());
        // <0 & =0
        assertEquals(e5 =
                new PredicateAbstractionDomainElement(DefaultImmutableSet
                        .<AbstractionPredicate> nil().add(ltZero).add(eqZero)),
                it.next());
        // >0
        assertEquals(e6 =
                new PredicateAbstractionDomainElement(DefaultImmutableSet
                        .<AbstractionPredicate> nil().add(gtZero)), it.next());
        // =0
        assertEquals(e7 =
                new PredicateAbstractionDomainElement(DefaultImmutableSet
                        .<AbstractionPredicate> nil().add(eqZero)), it.next());
        // <0
        assertEquals(e8 =
                new PredicateAbstractionDomainElement(DefaultImmutableSet
                        .<AbstractionPredicate> nil().add(ltZero)), it.next());
        // TOP
        assertEquals(e9 = PredicateAbstractionDomainElement.TOP, it.next());

        // There should be no further elements.
        assertFalse(it.hasNext());

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
        ArrayList<AbstractionPredicate> predicates =
                new ArrayList<AbstractionPredicate>();

        PredicateAbstractionLattice lattice =
                new PredicateAbstractionLattice(predicates);

        assertEquals(2, lattice.size());

        Iterator<AbstractDomainElement> it = lattice.iterator();

        // BOTTOM
        assertEquals(PredicateAbstractionDomainElement.BOTTOM, it.next());
        // TOP
        assertEquals(PredicateAbstractionDomainElement.TOP, it.next());

        // This should be all.
        assertFalse(it.hasNext());
    }

    private static AbstractionPredicate gtZero(final TermBuilder tb) {
        return AbstractionPredicate.create("_>0",
                (Term input) -> (tb.gt(input, tb.zero())));
    }

    private static AbstractionPredicate eqZero(final TermBuilder tb) {
        return AbstractionPredicate.create("_=0",
                (Term input) -> (tb.equals(input, tb.zero())));
    }

    private static AbstractionPredicate ltZero(final TermBuilder tb) {
        return AbstractionPredicate.create("_<0",
                (Term input) -> (tb.lt(input, tb.zero())));
    }

}

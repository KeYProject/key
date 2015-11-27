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

package de.uka.ilkd.key.axiom_abstraction.predicateabstraction;

import java.util.ArrayList;
import java.util.Iterator;

import org.key_project.util.collection.DefaultImmutableSet;

import de.uka.ilkd.key.axiom_abstraction.AbstractDomainElement;

/**
 * A lattice for all predicates accepting the given sort. This lattice consists
 * of n + 2 elements, where n is the number of applicable predicates. The first
 * element is a bottom element, the last a top element, and the elements in
 * between correspond to the given predicates.
 *
 * @author Dominic Scheurer
 */
public class SimplePredicateAbstractionLattice extends
        AbstractPredicateAbstractionLattice {
    private ArrayList<AbstractionPredicate> predicates =
            new ArrayList<AbstractionPredicate>();

    /**
     * Constructs a new {@link SimplePredicateAbstractionLattice} for the given
     * list of applicable predicates. The caller is responsible for making sure
     * that none of the predicates is valid.
     *
     * @param applicablePredicates
     *            The predicates to generate the lattice from.
     */
    public SimplePredicateAbstractionLattice(
            ArrayList<AbstractionPredicate> applicablePredicates) {
        super();

        assert predicates != null : "Do not call this constructor with a null argument.";
        this.predicates = applicablePredicates;

    }

    /*
     * (non-Javadoc)
     * 
     * @see
     * de.uka.ilkd.key.axiom_abstraction.AbstractDomainLattice#join(de.uka.ilkd
     * .key.axiom_abstraction.AbstractDomainElement,
     * de.uka.ilkd.key.axiom_abstraction.AbstractDomainElement)
     */
    @Override
    public AbstractDomainElement join(AbstractDomainElement a,
            AbstractDomainElement b) {
        /*
         * The join result is a PredicateAbstractionDomainElement constructed of
         * the intersection of the respective predicates.
         */
        return super.join(a, b, (set1, set2) -> (set1.intersect(set2)),
                set -> new SimplePredicateAbstractionDomainElement(set));
    }

    /**
     * The iterator for this lattice will first return the bottom element, then
     * the given predicates in the order in which they have been initially
     * supplied, and finally the top element.
     */
    @Override
    public Iterator<AbstractDomainElement> iterator() {
        return new Iterator<AbstractDomainElement>() {
            int idx = 0;

            @Override
            public boolean hasNext() {
                return idx < size();
            }

            @Override
            public AbstractDomainElement next() {
                final int oldIdx = idx;
                idx++;

                if (oldIdx == 0) {
                    return SimplePredicateAbstractionDomainElement.BOTTOM;
                }
                else if (oldIdx == size() - 1) {
                    return SimplePredicateAbstractionDomainElement.TOP;
                }
                else {
                    return new SimplePredicateAbstractionDomainElement(
                            DefaultImmutableSet.<AbstractionPredicate> nil()
                                    .add(predicates.get(oldIdx - 1)));
                }

            }
        };
    }

    /**
     * @return The number of elements in this lattice.
     */
    public int size() {
        // All predicates plus bottom and top elements.
        return predicates.size() + 2;
    }

    /*
     * (non-Javadoc)
     * 
     * @see java.lang.Object#equals(java.lang.Object)
     */
    @Override
    public boolean equals(Object obj) {
        return obj instanceof SimplePredicateAbstractionLattice
                && ((SimplePredicateAbstractionLattice) obj).predicates
                        .equals(this.predicates);
    }
    
    @Override
    public int hashCode() {
        return 31 * 3 + predicates.hashCode();
    }

    /*
     * (non-Javadoc)
     * 
     * @see java.lang.Object#toString()
     */
    @Override
    public String toString() {
        return "Simple Predicate Abstraction Lattice of size " + size()
                + " with predicates " + predicates.toString();
    }

    @Override
    protected AbstractPredicateAbstractionDomainElement getTopElem() {
        return SimplePredicateAbstractionDomainElement.TOP;
    }

    @Override
    protected AbstractPredicateAbstractionDomainElement getBottomElem() {
        return SimplePredicateAbstractionDomainElement.BOTTOM;
    }
}

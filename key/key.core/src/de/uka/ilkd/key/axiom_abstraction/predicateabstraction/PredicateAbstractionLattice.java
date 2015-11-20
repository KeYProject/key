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

import org.key_project.util.bitops.ImmutableFixedLengthBitSet;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableSet;
import org.key_project.util.collection.NotUniqueException;

import de.uka.ilkd.key.axiom_abstraction.AbstractDomainElement;
import de.uka.ilkd.key.axiom_abstraction.AbstractDomainLattice;
import de.uka.ilkd.key.axiom_abstraction.AbstractionPredicate;
import de.uka.ilkd.key.util.joinrule.JoinRuleUtils;

/**
 * A lattice for all predicates accepting the given sort. This lattice consists
 * of 2^n + 1 elements, where n is the number of applicable predicates. The last
 * element is a top element which is true for all inputs.
 * <p>
 * It may happen that certain elements of the lattice are equivalent to the
 * bottom element, since the respective combinations of predicates are
 * unsatisfiable. It should however not happen that combinations of predicates
 * are valid, that is they equal the top element. For efficiency reasons, the
 * lattice is only lazily generated on-demand by the iterator. Therefore, the
 * unsatisfiable combinations cannot be remove at generation time.
 *
 * @author Dominic Scheurer
 */
public class PredicateAbstractionLattice extends AbstractDomainLattice {
    private final ArrayList<AbstractionPredicate> predicates;

    /**
     * Constructs a new {@link PredicateAbstractionLattice} for the given list
     * of applicable predicates. The caller is responsible for making sure that
     * no combinations of predicates are valid.
     *
     * @param applicablePredicates
     */
    public PredicateAbstractionLattice(
            ArrayList<AbstractionPredicate> applicablePredicates) {
        super();
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

        // The join result is the intersection of the respective
        // predicates. If this is empty, then the top level element
        // is returned.

        assert a instanceof PredicateAbstractionDomainElement;
        assert b instanceof PredicateAbstractionDomainElement;

        PredicateAbstractionDomainElement pade1 =
                (PredicateAbstractionDomainElement) a;
        PredicateAbstractionDomainElement pade2 =
                (PredicateAbstractionDomainElement) b;

        if (pade1 == PredicateAbstractionDomainElement.TOP
                || pade2 == PredicateAbstractionDomainElement.TOP) {
            return PredicateAbstractionDomainElement.TOP;
        }

        if (pade1 == PredicateAbstractionDomainElement.BOTTOM) {
            return pade2;
        }

        if (pade2 == PredicateAbstractionDomainElement.BOTTOM) {
            return pade1;
        }

        ImmutableSet<AbstractionPredicate> preds1 = pade1.getPredicates();
        ImmutableSet<AbstractionPredicate> preds2 = pade2.getPredicates();
        
        ImmutableSet<AbstractionPredicate> intersection = preds1.intersect(preds2);
        
        if (intersection.size() == 0) {
            return PredicateAbstractionDomainElement.TOP;
        } else {
            return new PredicateAbstractionDomainElement(intersection);
        }
    }

    /**
     * The iterator for this lattice will first return the bottom element, then
     * all conjunctions of length n of the predicates, then all conjunctions of
     * length n-1, and so on, until finally the top element is returned.
     */
    @Override
    public Iterator<AbstractDomainElement> iterator() {
        return new PredicateLatticeIterator();
    }

    /**
     * @return The number of elements in this lattice.
     */
    public int size() {
        // All 2^n combinations (including bottom element) plus additional
        // top element.
        return JoinRuleUtils.intPow(2, predicates.size()) + 1;
    }

    /*
     * (non-Javadoc)
     * 
     * @see java.lang.Object#equals(java.lang.Object)
     */
    @Override
    public boolean equals(Object obj) {
        return obj instanceof PredicateAbstractionLattice
                && ((PredicateAbstractionLattice) obj).predicates
                        .equals(this.predicates);
    }

    /*
     * (non-Javadoc)
     * 
     * @see java.lang.Object#toString()
     */
    @Override
    public String toString() {
        return "Predicate Abstraction Lattice of size " + size()
                + " with predicates " + predicates.toString();
    }

    /**
     * @see PredicateAbstractionLattice#iterator()
     */
    private class PredicateLatticeIterator implements
            Iterator<AbstractDomainElement> {
        private int nrZeroes = -1;
        private int idx = 0;

        private final ArrayList<ArrayList<ImmutableFixedLengthBitSet>> bitSetsByNumZeroes =
                new ArrayList<ArrayList<ImmutableFixedLengthBitSet>>();

        /**
         * Constructs a new {@link PredicateLatticeIterator}; initializes the
         * bit sets for the iteration.
         */
        public PredicateLatticeIterator() {
            int numApplPreds = predicates.size();

            // We work with bit sets of length n (where n is the number of
            // predicates). Each bit represents a predicate; when the bit is
            // set to 1, the respective predicate should occur in the
            // conjunction.

            // Initialize the list.
            for (int i = 0; i < numApplPreds + 1; i++) {
                bitSetsByNumZeroes
                        .add(new ArrayList<ImmutableFixedLengthBitSet>());
            }

            // bitSet initially represents the number 0.
            ImmutableFixedLengthBitSet bitSet =
                    new ImmutableFixedLengthBitSet(numApplPreds);

            for (int i = 0; i < JoinRuleUtils.intPow(2, numApplPreds); i++) {
                int numZeroes = bitSet.getNumOfZeroBits();
                bitSetsByNumZeroes.get(numZeroes).add(bitSet);

                if (i < JoinRuleUtils.intPow(2, numApplPreds) - 1) {
                    bitSet = bitSet.inc();
                }
            }
        }

        /*
         * (non-Javadoc)
         * 
         * @see java.util.Iterator#hasNext()
         */
        @Override
        public boolean hasNext() {
            return nrZeroes < predicates.size() + 1;
        }

        /*
         * (non-Javadoc)
         * 
         * @see java.util.Iterator#next()
         */
        @Override
        public AbstractDomainElement next() {
            if (nrZeroes == -1) {
                nrZeroes++;
                return PredicateAbstractionDomainElement.BOTTOM;
            }

            if (nrZeroes == predicates.size()) {
                nrZeroes++;
                return PredicateAbstractionDomainElement.TOP;
            }

            ImmutableSet<AbstractionPredicate> predicatesForElem =
                    DefaultImmutableSet.<AbstractionPredicate> nil();

            ImmutableFixedLengthBitSet currBitSet =
                    bitSetsByNumZeroes.get(nrZeroes).get(idx);

            for (int nonZeroPosition : currBitSet.getNonzeroPositions()) {
                try {
                    predicatesForElem =
                            predicatesForElem.addUnique(predicates
                                    .get(nonZeroPosition));
                }
                catch (NotUniqueException e) {
                    // Not unique -- just don't add
                }
            }

            if (bitSetsByNumZeroes.get(nrZeroes).size() - 1 > idx) {
                idx++;
            }
            else {
                nrZeroes++;
                idx = 0;
            }

            return new PredicateAbstractionDomainElement(predicatesForElem);
        }

        /* (non-Javadoc)
         * @see java.util.Iterator#remove()
         */
        @Override
        public void remove() {
            throw new RuntimeException("Method remove not implemented");
        }

    }

}

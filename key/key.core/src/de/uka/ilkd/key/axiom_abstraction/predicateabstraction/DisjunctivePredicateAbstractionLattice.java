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
import de.uka.ilkd.key.axiom_abstraction.AbstractionPredicate;
import de.uka.ilkd.key.util.joinrule.JoinRuleUtils;

/**
 * A lattice for all predicates accepting the given sort. This lattice consists
 * of 2^n + 1 elements, where n is the number of applicable predicates. Each
 * element is a disjunction of the given predicates. The last element is a top
 * element which is true for all inputs.
 * <p>
 * It should however not happen that combinations of predicates are valid, that
 * is they equal the top element. For efficiency reasons, the lattice is only
 * lazily generated on-demand by the iterator. Therefore, the unsatisfiable
 * predicates cannot be removed at generation time.
 *
 * @author Dominic Scheurer
 */
public class DisjunctivePredicateAbstractionLattice extends
        AbstractPredicateAbstractionLattice {
    private ArrayList<AbstractionPredicate> predicates =
            new ArrayList<AbstractionPredicate>();

    /**
     * Constructs a new {@link DisjunctivePredicateAbstractionLattice} for the
     * given list of applicable predicates. The caller is responsible for making
     * sure that no combinations of predicates are valid.
     *
     * @param applicablePredicates
     *            The predicates to generate the lattice from.
     */
    public DisjunctivePredicateAbstractionLattice(
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
         * the union of the respective predicates.
         */
        return super.join(a, b, (set1, set2) -> (set1.union(set2)),
                set -> new DisjunctivePredicateAbstractionDomainElement(set));
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
        return obj instanceof DisjunctivePredicateAbstractionLattice
                && ((DisjunctivePredicateAbstractionLattice) obj).predicates
                        .equals(this.predicates);
    }
    
    @Override
    public int hashCode() {
        return 31 * 2 + predicates.hashCode();
    }

    /*
     * (non-Javadoc)
     * 
     * @see java.lang.Object#toString()
     */
    @Override
    public String toString() {
        return "Disjunctive Predicate Abstraction Lattice of size " + size()
                + " with predicates " + predicates.toString();
    }

    /**
     * @see DisjunctivePredicateAbstractionLattice#iterator()
     */
    private class PredicateLatticeIterator extends
            AbstractPredicateLatticeIterator {
        private int nrZeroes = -1;
        private int idx = 0;

        /**
         * Constructs a new {@link PredicateLatticeIterator}; initializes the
         * bit sets for the iteration.
         */
        public PredicateLatticeIterator() {
            super(predicates == null ? 0 : predicates.size());

            // When no predicates are chosen, it happens that the predicates
            // list is null in this inner class. This is sort of unexpected
            // behavior, since the the predicate abstraction lattice is (and
            // should be) never initialized with a null list. The lines below
            // fix this issue locally.
            if (predicates == null) {
                predicates = new ArrayList<AbstractionPredicate>();
            }
            
            nrZeroes = predicates.size();
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
                nrZeroes--;
                return DisjunctivePredicateAbstractionDomainElement.TOP;
            }

            if (nrZeroes == predicates.size()) {
                nrZeroes--;
                return DisjunctivePredicateAbstractionDomainElement.BOTTOM;
            }

            ImmutableSet<AbstractionPredicate> predicatesForElem =
                    DefaultImmutableSet.<AbstractionPredicate> nil();

            ImmutableFixedLengthBitSet currBitSet =
                    getBitSetsByNumZeroes().get(nrZeroes).get(idx);

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

            if (getBitSetsByNumZeroes().get(nrZeroes).size() - 1 > idx) {
                idx++;
            }
            else {
                nrZeroes--;
                idx = 0;
            }

            return new DisjunctivePredicateAbstractionDomainElement(predicatesForElem);
        }
    }

    @Override
    protected AbstractPredicateAbstractionDomainElement getTopElem() {
        return DisjunctivePredicateAbstractionDomainElement.TOP;
    }

    @Override
    protected AbstractPredicateAbstractionDomainElement getBottomElem() {
        return DisjunctivePredicateAbstractionDomainElement.BOTTOM;
    }
}

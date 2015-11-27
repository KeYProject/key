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
import java.util.function.BiFunction;
import java.util.function.Function;

import org.key_project.util.bitops.ImmutableFixedLengthBitSet;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.axiom_abstraction.AbstractDomainElement;
import de.uka.ilkd.key.axiom_abstraction.AbstractDomainLattice;
import de.uka.ilkd.key.util.joinrule.JoinRuleUtils;

/**
 * A super class for predicates abstraction lattices. Implements basic join
 * functionality and a template for an iterator initializing
 * ImmutableFixedLengthBitSets.
 *
 * @author Dominic Scheurer
 */
public abstract class AbstractPredicateAbstractionLattice extends
        AbstractDomainLattice {

    /**
     * Joins to abstract elements in the lattice.
     * 
     * @param a
     *            First domain element for the join.
     * @param b
     *            Second domain element for the join.
     * @param combiner
     *            The combination function (e.g., "AND") for the respective
     *            predicates of the inputs..
     * @param abstrElemConstructor
     *            A function constructing abstract domain elements from
     *            predicates.
     * @return The joined abstract domain element.
     */
    protected AbstractPredicateAbstractionDomainElement join(
            AbstractDomainElement a,
            AbstractDomainElement b,
            BiFunction<ImmutableSet<AbstractionPredicate>, ImmutableSet<AbstractionPredicate>, ImmutableSet<AbstractionPredicate>> combiner,
            Function<ImmutableSet<AbstractionPredicate>, AbstractPredicateAbstractionDomainElement> abstrElemConstructor) {

        // The join result is result of the application of the combination
        // function on the respective predicates. If this is empty, then
        // the top level element is returned (NOTE: Could also add a default
        // argument as parameter, but was not needed at the moment).

        assert a instanceof AbstractPredicateAbstractionDomainElement;
        assert b instanceof AbstractPredicateAbstractionDomainElement;

        AbstractPredicateAbstractionDomainElement pade1 =
                (AbstractPredicateAbstractionDomainElement) a;
        AbstractPredicateAbstractionDomainElement pade2 =
                (AbstractPredicateAbstractionDomainElement) b;

        if (pade1.isTopElem() || pade2.isTopElem()) {
            return getTopElem();
        }

        if (pade1 == getBottomElem()) {
            return pade2;
        }

        if (pade2 == getBottomElem()) {
            return pade1;
        }

        ImmutableSet<AbstractionPredicate> preds1 = pade1.getPredicates();
        ImmutableSet<AbstractionPredicate> preds2 = pade2.getPredicates();

        ImmutableSet<AbstractionPredicate> combination =
                combiner.apply(preds1, preds2);

        if (combination.size() == 0) {
            return getTopElem();
        }
        else {
            return abstrElemConstructor.apply(combination);
        }
    }

    /**
     * @return The top element of the lattice.
     */
    protected abstract AbstractPredicateAbstractionDomainElement getTopElem();

    /**
     * @return The bottom element of the lattice.
     */
    protected abstract AbstractPredicateAbstractionDomainElement getBottomElem();

    /**
     * An abstract iterator which basically only sets up the bit sets
     * used for building up complex iterators.
     *
     * @author Dominic Scheurer
     */
    protected abstract class AbstractPredicateLatticeIterator implements
            Iterator<AbstractDomainElement> {

        private final ArrayList<ArrayList<ImmutableFixedLengthBitSet>> bitSetsByNumZeroes =
                new ArrayList<ArrayList<ImmutableFixedLengthBitSet>>();

        /**
         * Constructs a new {@link AbstractPredicateLatticeIterator};
         * initializes the bit sets for the iteration.
         * 
         * @param numApplPreds
         *            The number of applicable predicates for the lattice.
         */
        public AbstractPredicateLatticeIterator(int numApplPreds) {
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

        /**
         * @return The list of bit sets for all given numbers of zeroes occurrences.
         */
        public ArrayList<ArrayList<ImmutableFixedLengthBitSet>> getBitSetsByNumZeroes() {
            return bitSetsByNumZeroes;
        }

        /*
         * (non-Javadoc)
         * 
         * @see java.util.Iterator#remove()
         */
        @Override
        public void remove() {
            throw new RuntimeException("Method \"remove\" not implemented");
        }
    }

}

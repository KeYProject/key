/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.prover.strategy.costbased.feature;

import org.key_project.logic.Term;
import org.key_project.logic.TermOrdering;
import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.util.collection.ImmutableList;

/// Abstract superclass for features comparing terms (in particular polynomials or monomials) using
/// the term ordering
public abstract class SmallerThanFeature<GOAL extends ProofGoal<GOAL>>
        extends BinaryTacletAppFeature<GOAL> {

    private final TermOrdering termOrdering;

    protected SmallerThanFeature(TermOrdering termOrdering) {
        this.termOrdering = termOrdering;
    }

    protected boolean lessThan(Term t1, Term t2,
            PosInOccurrence focus, GOAL currentGoal) {
        return compare(t1, t2) < 0;
    }

    protected final int compare(Term t1, Term t2) {
        return termOrdering.compare(t1, t2);
    }

    /// @return `true` iff each element of `list1` is strictly smaller than all
    /// elements of `list2`
    protected final boolean lessThan(ImmutableList<Term> list1, ImmutableList<Term> list2,
            PosInOccurrence focus, GOAL currentGoal) {
        if (list2.isEmpty()) {
            return false;
        }
        for (Term aList1 : list1) {
            for (Term aList2 : list2) {
                if (!lessThan(aList1, aList2, focus, currentGoal)) {
                    return false;
                }
            }
        }
        return true;
    }

    protected abstract static class Collector {
        private ImmutableList<Term> terms = ImmutableList.nil();

        protected void addTerm(Term mon) {
            terms = terms.prepend(mon);
        }

        public ImmutableList<Term> getResult() {
            return terms;
        }
    }
}

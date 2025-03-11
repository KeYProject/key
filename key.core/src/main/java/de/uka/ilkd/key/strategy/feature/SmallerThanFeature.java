/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.logic.LexPathOrdering;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermOrdering;
import de.uka.ilkd.key.proof.Goal;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;


/**
 * Abstract superclass for features comparing terms (in particular polynomials or monomials) using
 * the term ordering
 */
public abstract class SmallerThanFeature extends BinaryTacletAppFeature {

    private final TermOrdering termOrdering = new LexPathOrdering();

    protected boolean lessThan(Term t1, Term t2, PosInOccurrence focus, Goal currentGoal) {
        return compare(t1, t2) < 0;
    }

    protected final int compare(Term t1, Term t2) {
        return termOrdering.compare(t1, t2);
    }

    /**
     * @return <code>true</code> iff each element of <code>list1</code> is strictly smaller than all
     *         elements of <code>list2</code>
     */
    protected final boolean lessThan(ImmutableList<Term> list1, ImmutableList<Term> list2,
            PosInOccurrence focus, Goal currentGoal) {
        if (list2.isEmpty()) {
            return false;
        }
        for (Term aList1 : list1) {
            final Term te1 = aList1;
            for (Term aList2 : list2) {
                if (!lessThan(te1, aList2, focus, currentGoal)) {
                    return false;
                }
            }
        }
        return true;
    }

    protected abstract static class Collector {

        private ImmutableList<Term> terms = ImmutableSLList.nil();

        protected void addTerm(Term mon) {
            terms = terms.prepend(mon);
        }

        public ImmutableList<Term> getResult() {
            return terms;
        }

    }

}

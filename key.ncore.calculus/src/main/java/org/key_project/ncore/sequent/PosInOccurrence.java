/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.ncore.sequent;

import org.key_project.logic.IntIterator;
import org.key_project.logic.PosInTerm;
import org.key_project.logic.Term;

public class PosInOccurrence {
    public static PosInOccurrence findInSequent(Sequent seq, int formulaNumber, PosInTerm pos) {
        return new PosInOccurrence(seq.getFormulaByNr(formulaNumber), pos,
            seq.numberInAntec(formulaNumber));
    }

    /**
     * the constrained formula the pos in occurrence describes
     */
    private final SequentFormula sequentFormula;
    /**
     * is true iff the position is in the antecedent of a sequent.
     */
    private final boolean inAntec;

    /** the position in sequentFormula.formula() */
    private final PosInTerm posInTerm;

    /**
     * The subterm this object points to, or <code>null</code>
     */
    private volatile Term subTermCache = null;

    public PosInOccurrence(SequentFormula sequentFormula, PosInTerm posInTerm, boolean inAntec) {
        assert posInTerm != null;
        assert sequentFormula != null;
        this.inAntec = inAntec;
        this.sequentFormula = sequentFormula;
        this.posInTerm = posInTerm;
    }

    /**
     * returns the SequentFormula that determines the occurrence of this PosInOccurrence
     */
    public SequentFormula sequentFormula() {
        return sequentFormula;
    }

    /**
     * @return Depth of the represented position within a formula; top-level positions
     *         (<code>isTopLevel()</code> have depth zero
     */
    public int depth() {
        return posInTerm().depth();
    }

    /**
     * creates a new PosInOccurrence that has exactly the same state as this object except the
     * PosInTerm is new and walked down the specified subterm, as specified in method down of
     * {@link PosInTerm}.
     */
    public PosInOccurrence down(int i) {
        return new PosInOccurrence(sequentFormula, posInTerm.down(i), inAntec);
    }

    /**
     * @return the number/index of the deepest subterm that this <code>PosInOccurrence</code> points
     *         to. If the position is top-level, the result will be <code>-1</code>
     */
    public int getIndex() {
        return posInTerm.getIndex();
    }

    /**
     * returns true iff the occurrence is in the antecedent of a sequent.
     */
    public boolean isInAntec() {
        return inAntec;
    }

    public boolean isTopLevel() {
        return posInTerm == PosInTerm.getTopLevel();
    }

    /**
     * The usage of this method is strongly discouraged, use {@link PosInOccurrence#iterator}
     * instead. describes the exact occurrence of the referred term inside
     * {@link SequentFormula#formula()}
     *
     * @return the position in the formula of the SequentFormula of this PosInOccurrence.
     */
    public PosInTerm posInTerm() {
        return posInTerm;
    }

    /**
     * returns the subterm this object points to
     */
    public Term subTerm() {
        if (subTermCache == null) {
            subTermCache = posInTerm.getSubTerm(sequentFormula.formula());
        }
        return subTermCache;
    }

    public PIOPathIterator iterator() {
        return new PIOPathIteratorImpl();
    }

    private final class PIOPathIteratorImpl implements PIOPathIterator {
        int child;
        int count = 0;
        IntIterator currentPathIt;
        Term currentSubTerm = null;

        private PIOPathIteratorImpl() {
            currentPathIt = posInTerm().iterator();
        }

        /**
         * @return the number of the next child on the path, or <code>-1</code> if no further child
         *         exists (this is the number that was also returned by the last call of
         *         <code>next()</code>)
         */
        public int getChild() {
            return child;
        }

        public String toString() {
            return "Term " + posInTerm() + " of " + sequentFormula();
        }

        /**
         * @return the current position within the term (i.e. corresponding to the latest
         *         <code>next()</code>-call)
         */
        public PosInOccurrence getPosInOccurrence() {
            // the object is created only now to make the method
            // <code>next()</code> faster

            final PosInOccurrence pio;
            pio = new PosInOccurrence(sequentFormula, posInTerm.firstN(count - 1), inAntec);


            return pio;
        }

        /**
         * @return the current subterm this object points to (i.e. corresponding to the latest
         *         <code>next()</code>-call); this method satisfies
         *         <code>getPosInOccurrence().subTerm()==getSubTerm()</code>
         */
        public Term getSubTerm() {
            return currentSubTerm;
        }

        public boolean hasNext() {
            return currentPathIt != null;
        }

        /**
         * @return the number of the next child on the path, or <code>-1</code> if no further child
         *         exists
         */
        public int next() {
            int res;

            if (currentSubTerm == null) {
                currentSubTerm = sequentFormula.formula();
            } else {
                currentSubTerm = currentSubTerm.sub(child);
            }

            if (currentPathIt.hasNext()) {
                res = currentPathIt.next();
            } else {
                res = -1;
                currentPathIt = null;
            }

            child = res;
            ++count;
            return res;
        }
    }
}

/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.sequent;

import org.key_project.logic.IntIterator;
import org.key_project.logic.PosInTerm;
import org.key_project.logic.Term;

public class PosInOccurrence {
    public static PosInOccurrence findInSequent(Sequent seq, int formulaNumber, PosInTerm pos) {
        return new PosInOccurrence(seq.getFormulaByNr(formulaNumber), pos,
            seq.numberInAntec(formulaNumber));
    }

    // saves 8 bytes (due to alignment issues) per instance if we use a
    // short here instead of an int
    private final short hashCode;

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
        this.hashCode = (short) (sequentFormula.hashCode() * 13 + posInTerm.hashCode());
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
     * PosInTerm is new and walked up the specified subterm, as specified in method up of
     * {@link PosInTerm}.
     */
    public PosInOccurrence up() {
        assert !isTopLevel() : "not possible to go up from top level position";
        return new PosInOccurrence(sequentFormula, posInTerm.up(), inAntec);
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
     * Ascend to the top node of the formula this object points to
     */
    public PosInOccurrence topLevel() {
        if (isTopLevel()) {
            return this;
        }
        return new PosInOccurrence(sequentFormula, PosInTerm.getTopLevel(), inAntec);
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

    /**
     * compares this PosInOccurrence with another PosInOccurrence and returns true if both describe
     * the same occurrence
     */
    public boolean eqEquals(Object obj) {
        if (!(obj instanceof PosInOccurrence cmp)) {
            return false;
        }

        if (!sequentFormula.equals(cmp.sequentFormula)) {
            return false;
        }

        return equalsHelp(cmp);
    }

    /**
     * Contrary to <code>eqEquals</code>, this method returns true only for pio objects that point
     * to the same (identical) formula
     *
     * @param obj the Object to which this one is compared
     * @return true if both objects are equal
     */
    @Override
    public boolean equals(Object obj) {
        if (!(obj instanceof PosInOccurrence cmp)) {
            return false;
        }

        // NB: the class <code>NonDuplicateAppFeature</code> depends on the usage
        // of <code>!=</code> in this condition
        if (sequentFormula() != cmp.sequentFormula()) {
            return false;
        }

        return equalsHelp(cmp);
    }

    private boolean equalsHelp(final PosInOccurrence cmp) {
        if (inAntec == cmp.inAntec) {
            return posInTerm.equals(cmp.posInTerm);
        }
        return false;
    }

    @Override
    public int hashCode() {
        return hashCode;
    }

    /**
     * Replace the formula this object points to with the new formula given
     *
     * @param p_newFormula the new formula
     * @return a <code>PosInOccurrence</code> object that points to the same position within the
     *         formula <code>p_newFormula</code> as this object does within the formula
     *         <code>constrainedFormula()</code>. It is not tested whether this position exists
     *         within <code>p_newFormula</code>
     */
    public PosInOccurrence replaceSequentFormula(SequentFormula p_newFormula) {
        assert p_newFormula != null;
        if (p_newFormula == sequentFormula) {
            return this;
        }
        return new PosInOccurrence(p_newFormula, posInTerm, inAntec);
    }

    public PIOPathIterator iterator() {
        return new PIOPathIteratorImpl();
    }

    /** toString */
    public String toString() {
        return "Term " + posInTerm() + " of " + sequentFormula();
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

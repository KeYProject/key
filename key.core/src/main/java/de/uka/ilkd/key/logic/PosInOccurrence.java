/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic;

/**
 * This class describes a position in an occurrence of a term. A Term and a PosInTerm
 * determine an object of this class exactly.
 */
public final class PosInOccurrence {

    public static PosInOccurrence findInSequent(Sequent seq, int formulaNumber, PosInTerm pos) {
        return new PosInOccurrence(seq.getFormulabyNr(formulaNumber), pos,
            seq.numberInAntec(formulaNumber));
    }

    /**
     * the constrained formula the pos in occurrence describes
     */
    private final Term sequentLevelFormula;

    // saves 8 bytes (due to alignment issues) per instance if we use a
    // short here instead of an int
    private final short hashCode;

    /**
     * is true iff the position is in the antecedent of a sequent.
     */
    private final boolean inAntec;

    /** the position in Term.formula() */
    private final PosInTerm posInTerm;

    /**
     * The subterm this object points to, or <code>null</code>
     */
    private volatile Term subTermCache = null;

    public PosInOccurrence(Term sequentLevelFormula, PosInTerm posInTerm, boolean inAntec) {
        assert posInTerm != null;
        assert sequentLevelFormula != null;
        this.inAntec = inAntec;
        this.sequentLevelFormula = sequentLevelFormula;
        this.posInTerm = posInTerm;
        this.hashCode = (short) (sequentLevelFormula.hashCode() * 13 + posInTerm.hashCode());
    }

    /**
     * returns the Term that determines the occurrence of this PosInOccurrence
     */
    public Term sequentLevelFormula() {
        return sequentLevelFormula;
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
     * {@link de.uka.ilkd.key.logic.PosInTerm}.
     */
    public PosInOccurrence down(int i) {
        return new PosInOccurrence(sequentLevelFormula, posInTerm.down(i), inAntec);
    }

    /**
     * compares this PosInOccurrence with another PosInOccurrence and returns true if both describe
     * the same occurrence
     */
    public boolean eqEquals(Object obj) {
        if (!(obj instanceof PosInOccurrence cmp)) {
            return false;
        }

        if (!sequentLevelFormula.equals(cmp.sequentLevelFormula)) {
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
        if (sequentLevelFormula() != cmp.sequentLevelFormula()) {
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

    /**
     * @return the number/index of the deepest subterm that this <code>PosInOccurrence</code> points
     *         to. If the position is top-level, the result will be <code>-1</code>
     */
    public int getIndex() {
        return posInTerm.getIndex();
    }

    public int hashCode() {
        return hashCode;
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
     * List all subterms between the root and the position this objects points to; the first term is
     * the whole sequent level <code>formula</code>, the last one
     * <code>subTerm()</code>
     *
     * @return an iterator that walks from the root of the term to the position this
     *         <code>PosInOccurrence</code>-object points to
     */
    public PIOPathIterator iterator() {
        return new PIOPathIteratorImpl();
    }

    /**
     * The usage of this method is strongly discouraged, use {@link PosInOccurrence#iterator}
     * instead. describes the exact occurrence of the referred term
     *
     * @return the position in the formula of the Term of this PosInOccurrence.
     */
    public PosInTerm posInTerm() {
        return posInTerm;
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
    public PosInOccurrence replaceConstrainedFormula(Term p_newFormula) {
        assert p_newFormula != null;
        if (p_newFormula == sequentLevelFormula) {
            return this;
        }
        return new PosInOccurrence(p_newFormula, posInTerm, inAntec);
    }

    /**
     * returns the subterm this object points to
     */
    public Term subTerm() {
        if (subTermCache == null) {
            subTermCache = posInTerm.getSubTerm(sequentLevelFormula);
        }
        return subTermCache;
    }

    /**
     * Ascend to the top node of the formula this object points to
     */
    public PosInOccurrence topLevel() {
        if (isTopLevel()) {
            return this;
        }
        return new PosInOccurrence(sequentLevelFormula, PosInTerm.getTopLevel(), inAntec);
    }


    /** toString */
    public String toString() {
        return "Term " + posInTerm() + " of " + sequentLevelFormula();
    }



    /**
     * Ascend to the parent node
     */
    public PosInOccurrence up() {
        assert !isTopLevel() : "not possible to go up from top level position";

        return new PosInOccurrence(sequentLevelFormula, posInTerm.up(), inAntec);

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

        /**
         * @return the current position within the term (i.e. corresponding to the latest
         *         <code>next()</code>-call)
         */
        public PosInOccurrence getPosInOccurrence() {
            // the object is created only now to make the method
            // <code>next()</code> faster

            final PosInOccurrence pio;
            pio = new PosInOccurrence(sequentLevelFormula, posInTerm.firstN(count - 1), inAntec);


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
                currentSubTerm = sequentLevelFormula;
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

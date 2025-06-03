/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.calculus;

import de.uka.ilkd.key.logic.equality.RenamingTermProperty;

import org.key_project.prover.sequent.SemisequentChangeInfo;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

class Semisequent extends org.key_project.prover.sequent.Semisequent {

    static final org.key_project.prover.sequent.Semisequent EMPTY_SEMISEQUENT = new Empty();

    /**
     * Create a new Semisequent from an ordered collection of formulas.
     * The provided list must be redundancy free, i.e., the created sequent must be exactly
     * the same as when creating the sequent by subsequently inserting all formulas
     *
     * @param seqList list of sequent formulas
     */
    Semisequent(ImmutableList<SequentFormula> seqList) {
        super(seqList);
    }

    protected Semisequent() {
        super();
    }

    protected boolean isRedundant(SequentFormula existingFormula, SequentFormula checkedFormula) {
        return RenamingTermProperty.RENAMING_TERM_PROPERTY
                .equalsModThisProperty(existingFormula.formula(), checkedFormula.formula());
    }

    // inner class used to represent an empty semisequent
    private static class Empty extends Semisequent {
        public Empty() {
            super();
        }

        /**
         * inserts the element always at index 0 ignores the first argument
         *
         * @param idx int encoding the place the element has to be put
         * @param sequentFormula {@link SequentFormula} to be inserted
         * @return semisequent change information object with new semisequent with sequentFormula at
         *         place idx
         */
        @Override
        public SemisequentChangeInfo insert(int idx, SequentFormula sequentFormula) {
            return insertFirst(sequentFormula);
        }

        /**
         * inserts the element at index 0
         *
         * @param sequentFormula {@link SequentFormula} to be inserted
         * @return semisequent change information object with new semisequent with sequentFormula at
         *         place idx
         */
        @Override
        public SemisequentChangeInfo insertFirst(SequentFormula sequentFormula) {
            final SemisequentChangeInfo sci = new SemisequentChangeInfo(
                ImmutableSLList.singleton(sequentFormula));
            sci.addedFormula(0, sequentFormula);
            return sci;
        }

        /**
         * inserts the element at the end of the semisequent
         *
         * @param sequentFormula {@link SequentFormula} to be inserted
         * @return semisequent change information object with new semisequent with sequentFormula at
         *         place idx
         */
        @Override
        public SemisequentChangeInfo insertLast(SequentFormula sequentFormula) {
            return insertFirst(sequentFormula);
        }

        /**
         * is this a semisequent that contains no formulas
         *
         * @return true if the semisequent contains no formulas
         */
        @Override
        public boolean isEmpty() {
            return true;
        }

        /**
         * replaces the element at place idx with sequentFormula
         *
         * @param idx an int specifying the index of the element that has to be replaced
         * @param sequentFormula the {@link SequentFormula} replacing the old element at index idx
         * @return semisequent change information object with new semisequent with sequentFormula at
         *         place idx
         */
        @Override
        public SemisequentChangeInfo replace(int idx, SequentFormula sequentFormula) {
            return insertFirst(sequentFormula);
        }

        /** @return int counting the elements of this semisequent */
        @Override
        public int size() {
            return 0;
        }

        /**
         * removes an element
         *
         * @param idx int being the index of the element that has to be removed
         * @return semisequent change information object with an empty semisequent as result
         */
        @Override
        public SemisequentChangeInfo remove(int idx) {
            return new SemisequentChangeInfo(ImmutableSLList.nil());
        }

        /**
         * returns index of a {@link SequentFormula}
         *
         * @param sequentFormula the {@link SequentFormula} the index want to be determined
         * @return index of sequentFormula
         */
        @Override
        public int indexOf(SequentFormula sequentFormula) {
            return -1;
        }

        /**
         * gets the element at a specific index
         *
         * @param idx int representing the index of the element we want to have
         * @return {@link SequentFormula} found at index idx
         */
        @Override
        public SequentFormula get(int idx) {
            return null;
        }

        /**
         * @return the first SequentFormula of this Semisequent
         */
        @Override
        public SequentFormula getFirst() {
            return null;
        }

        /**
         * checks if a {@link SequentFormula} is in this Semisequent
         *
         * @param sequentFormula the {@link SequentFormula} to look for
         * @return true iff. sequentFormula has been found in this Semisequent
         */
        @Override
        public boolean contains(SequentFormula sequentFormula) {
            return false;
        }

        @Override
        public boolean equals(Object other) {
            return other == this;
        }

        @Override
        public int hashCode() {
            return 34567;
        }

        /** @return String representation of this Semisequent */
        @Override
        public String toString() {
            return "[]";
        }
    }
}

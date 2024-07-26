/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.logic;

import java.util.Iterator;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import org.jspecify.annotations.NonNull;

public class Semisequent implements Iterable<SequentFormula> {
    /** the empty semisequent (using singleton pattern) */
    public static final Semisequent EMPTY_SEMISEQUENT = new Empty();
    /** list with the {@link SequentFormula}s of the Semisequent */
    private final ImmutableList<SequentFormula> seqList;

    /** used by inner class Empty */
    private Semisequent() {
        seqList = ImmutableSLList.nil();
    }

    /**
     * creates a new Semisequent with the Semisequent elements in seqList
     */
    public Semisequent(SequentFormula seqFormula) {
        assert seqFormula != null;
        this.seqList = ImmutableSLList.<SequentFormula>nil().append(seqFormula);
    }

    /**
     * is this a semisequent that contains no formulas
     *
     * @return true if the semisequent contains no formulas
     */
    public boolean isEmpty() {
        return seqList.isEmpty();
    }

    /**
     * gets the element at a specific index
     *
     * @param idx int representing the index of the element we want to have
     * @return {@link SequentFormula} found at index idx
     * @throws IndexOutOfBoundsException if idx is negative or greater or equal to
     *         {@link Sequent#size()}
     */
    public SequentFormula get(int idx) {
        if (idx < 0 || idx >= seqList.size()) {
            throw new IndexOutOfBoundsException();
        }
        return seqList.take(idx).head();
    }

    /** @return the first {@link SequentFormula} of this Semisequent */
    public SequentFormula getFirst() {
        return seqList.head();
    }

    /**
     * returns iterator about the elements of the sequent
     *
     * @return Iterator<SequentFormula>
     */
    @Override
    public @NonNull Iterator<SequentFormula> iterator() {
        return seqList.iterator();
    }

    public ImmutableList<SequentFormula> asList() {
        return seqList;
    }

    /** @return int counting the elements of this semisequent */
    public int size() {
        return seqList.size();
    }


    @Override
    public boolean equals(Object o) {
        if (!(o instanceof Semisequent)) {
            return false;
        }
        return seqList.equals(((Semisequent) o).seqList);
    }

    // inner class used to represent an empty semisequent
    private static class Empty extends Semisequent {

        private Empty() {
            super();
        }
    }
}

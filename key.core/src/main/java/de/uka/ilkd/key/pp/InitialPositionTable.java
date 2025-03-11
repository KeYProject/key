/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.pp;

import de.uka.ilkd.key.logic.IntIterator;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.SequentFormula;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

/**
 * An InitialPositionTable is a PositionTable that describes the beginning of the element/subelement
 * relationship. Thus, an InitialPositionTable describes the information on where the
 * {@link SequentFormula}e of a sequent are located. It is the root of the tree of PositionTables
 * and may be asked for a PosInSequent for a given index position and a given Sequent.
 *
 * <p>
 * For simplicity, the an InitialPositionTable has only one row. The various constrained formulae of
 * a sequent are located one level below. In other words the whole sequent is not represented by an
 * empty position list but by the list [0].
 */
public class InitialPositionTable extends PositionTable {

    private ImmutableList<Range> updateRanges = ImmutableSLList.nil();

    /** Ranges of keywords */
    private ImmutableList<Range> keywordRanges = ImmutableSLList.nil();
    /** Ranges of java blocks */
    private ImmutableList<Range> javaBlockRanges = ImmutableSLList.nil();

    /**
     * creates a new Initial PositionTable.
     */
    public InitialPositionTable() {
        super(1);
    }

    /**
     * Returns the PosInSequent for a given char position in a sequent.
     *
     * @param index the char position that points to the wanted position in sequent
     * @param filter the sequent print filter from that was used to print the sequent
     *
     */
    public PosInSequent getPosInSequent(int index, SequentPrintFilter filter) {
        if (index < startPos[0] || index >= endPos[0]) {
            return null;
        }

        ImmutableList<Integer> posList = pathForIndex(index);

        PosInSequent pis = getTopPIS(posList, filter);

        Range r = rangeForIndex(index);
        pis.setBounds(r);
        Range firstStatement = firstStatementRangeForIndex(index);
        if (firstStatement != null) {
            pis.setFirstJavaStatementRange(firstStatement);
        }
        return pis;
    }

    /**
     * Returns a PosInSequent for a given position list, but without filling in the bounds. It is
     * assumed that this is the top level position table for a sequent.
     *
     * @param posList the position list that navigates through the position tables.
     * @param filter the sequent print filter from that was used to print the sequent
     */
    private PosInSequent getTopPIS(ImmutableList<Integer> posList, SequentPrintFilter filter) {
        if (posList.isEmpty() || posList.tail().isEmpty()) {
            return PosInSequent.createSequentPos();
        } else {
            return children[0].getSequentPIS(posList.tail(), filter);
        }
    }


    /**
     * Returns the path for a given PosInOccurrence. This is built up from the initial 0, the number
     * of the SequentFormula in the sequent, the position in the constrained formula, and possibly
     * inside a Metavariable instantiation.
     *
     * @param pio the given PosInOccurrence
     * @param filter the current filter
     * @return the path for the given pio
     */
    public ImmutableList<Integer> pathForPosition(PosInOccurrence pio, SequentPrintFilter filter) {
        ImmutableList<Integer> p = ImmutableSLList.nil();
        p = prependPathInFormula(p, pio);
        int index = indexOfCfma(pio.sequentFormula(), filter);
        if (index == -1) {
            return null;
        }
        p = p.prepend(index);
        p = p.prepend(0);
        return p;
    }

    private ImmutableList<Integer> prependPathInFormula(ImmutableList<Integer> p,
            PosInOccurrence pio) {
        IntIterator pit = pio.posInTerm().reverseIterator();
        while (pit.hasNext()) {
            p = p.prepend(pit.next());
        }
        return p;
    }


    /**
     * Returns the index of the constrained formula in the sequent as printed.
     *
     * @param cfma the sequent formula
     * @param filter the current filter
     * @return the index of the given formula in the sequent as printed
     */
    private int indexOfCfma(SequentFormula cfma, SequentPrintFilter filter) {
        ImmutableList<SequentPrintFilterEntry> list =
            filter.getFilteredAntec().append(filter.getFilteredSucc());
        int k;
        for (k = 0; !list.isEmpty(); k++, list = list.tail()) {
            if (list.head().getOriginalFormula() == cfma) {
                return k;
            }
        }
        return -1;
    }

    /**
     * Returns the character range of the `lowest' subtable that includes <code>index</code> in its
     * range.
     *
     * @param index the character index to search for.
     */
    public Range rangeForIndex(int index) {
        return rangeForIndex(index, endPos[0]);
    }

    /**
     * Returns the character range for the subtable indicated by the given integer list.
     */
    public Range rangeForPath(ImmutableList<Integer> path) {
        return rangeForPath(path, endPos[0]);
    }

    /**
     * Adds a range for a keyword to the keyword list.
     *
     * @param r Range of keyword to be added
     */
    public void addKeywordRange(Range r) {
        keywordRanges = keywordRanges.prepend(r);
    }

    /**
     * @return ranges of keywords printed
     */
    public Range[] getKeywordRanges() {
        return keywordRanges.toArray(new Range[keywordRanges.size()]);
    }

    /**
     * Adds a range for a java block to the java block list.
     *
     * @param r Range of keyword to be added
     */
    public void addJavaBlockRange(Range r) {
        javaBlockRanges = javaBlockRanges.prepend(r);
    }

    /**
     * @return ranges of java blocks printed
     */
    public Range[] getJavaBlockRanges() {
        return javaBlockRanges.toArray(new Range[javaBlockRanges.size()]);
    }

    public void addUpdateRange(Range r) {
        updateRanges = updateRanges.prepend(r);
    }

    public Range[] getUpdateRanges() {
        return updateRanges.toArray(new Range[updateRanges.size()]);
    }
}

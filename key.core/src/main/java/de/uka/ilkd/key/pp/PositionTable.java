/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.pp;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.SequentFormula;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

/**
 * A PositionTable describes the start and end positions of substrings of a String in order to get a
 * PosInSequent from an int describing a position in a string representing a Term or a Sequent, etc.
 * A PositionTable therefore represents a table consisting of two columns of type int (start and end
 * position) and a reference to another PositionTable representing the position information for that
 * substring. A PositionTable is valid (in order to support efficient putting of new entries to the
 * table and an efficient search for a Position), if the last entry that has been set is (s, e, x)
 * and the next entry is (s', e', x') with s'>e.
 *
 * <p>
 * Positions are reckoned with start positions inclusive and end positions exclusive. Start and end
 * positions are relative to each subterm.
 */
public class PositionTable {

    // the start positions of the direct subterms (or parts of sequent, etc.)
    protected final int[] startPos;

    // the end positions of the direct subterms (or parts of sequent, etc.)
    protected final int[] endPos;

    /** the PositionTables for the direct subterms (or parts of sequent, etc.) */
    protected final PositionTable[] children;

    // the current active entry number.
    // When a new "in-order" element is started, the counter is increased.
    // A new "out-of-order" element resets the counter to a fresh value.
    private int currentEntry = -1;

    // the number of rows in the above arrays. Equals the number of direct
    // subterms (or parts of sequent, etc.)
    private final int rows;

    /**
     * creates a new PositionTable with the number of subterms (or number of SequentFormula in a
     * Semisequent, or the number of Semisequents in a Sequent, etc.)
     *
     * @param rows the number of direct sub-elements in the term whose position information is
     *        represented by the constructed object.
     */
    public PositionTable(int rows) {
        this.rows = rows;
        startPos = new int[rows];
        endPos = new int[rows];
        children = new PositionTable[rows];
        for (int i = 0; i < rows; i++) {
            startPos[i] = -1;
            endPos[i] = -1;
            children[i] = null;
        }
    }

    /**
     * returns the m with startPos[m]<=index<=endPos[m]. -1 if no such m exists.
     */
    private int searchEntry(int index) {

        // linear search:
        for (int m = 0; m < rows; m++) {
            if ((startPos[m] <= index) && (index < endPos[m])) {
                return m;
            }
        }

        // binary search (ordered arrays are precondition!), NOT CHECKED SO FAR:
        /*
         * int l=0; int r=rows-1; int m; while (r<l) { m=(l+r)/2; if ((startPos[m]<=index) &&
         * (endPos[m]>index)) { return m; } if (index<startPos[m]) { r=m; } else { l=m; } }
         */
        return -1;
    }

    /**
     * Returns the path to the `lowest' position table that includes <code>index</code> in its
     * range.
     */
    protected ImmutableList<Integer> pathForIndex(int index) {
        int sub = searchEntry(index);
        if (sub == -1) {
            return ImmutableSLList.nil();
        } else {
            return children[sub].pathForIndex(index - startPos[sub]).prepend(sub);
        }
    }

    /**
     * Returns the character range of the `lowest' subtable that includes <code>index</code> in its
     * range.
     *
     * @param index the character index to search for.
     * @param length the length of the whole string corresponding to this position table. Needed in
     *        case it turns out the index belongs to the top level.
     *
     * @return the character range of the `lowest' subtable that includes <code>index</code> in its
     *         range.
     */
    public Range rangeForIndex(int index, int length) {
        int sub = searchEntry(index);
        if (sub == -1) {
            return new Range(0, length);
        } else {
            Range r =
                children[sub].rangeForIndex(index - startPos[sub], endPos[sub] - startPos[sub]);
            r.start += startPos[sub];
            r.end += startPos[sub];
            return r;
        }
    }

    /**
     * Returns the character range of the first java statement in a program modality for the
     * `lowest' subtable that includes <code>index</code> in its range. If the lowest subtable does
     * not correspond to a program modality, it returns null.
     */
    public Range firstStatementRangeForIndex(int index) {
        int sub = searchEntry(index);
        if (sub == -1) {
            return getFirstStatementRange();
        } else {
            Range r = children[sub].firstStatementRangeForIndex(index - startPos[sub]);
            if (r != null) {
                r.start += startPos[sub];
                r.end += startPos[sub];
            }
            return r;
        }
    }

    /**
     * @return Returns the character range of the first java statement in a program modality for
     *         <i>this</i>position table. If this is not a program modality, returns null. Note that
     *         this will be overridden in the subclass {@link ModalityPositionTable}.
     */
    public Range getFirstStatementRange() {
        return null;
    }

    /**
     * @param path the given integer list, i.e. path
     * @param length length of the range
     * @return Returns the character range for the subtable indicated by the given integer list.
     */
    public Range rangeForPath(ImmutableList<Integer> path, int length) {
        if (path.isEmpty()) {
            return new Range(0, length);
        } else {
            int sub = path.head();
            Range r = children[sub].rangeForPath(path.tail(), endPos[sub] - startPos[sub]);
            r.start += startPos[sub];
            r.end += startPos[sub];
            return r;
        }
    }

    /**
     * sets end in the position table to the next free end entry in the position table and sets the
     * given PositionTable as child of the sub-element finished by putting this end position
     *
     * @param end char position that ends the sub-element started by the corresponding start entry
     *        in the position table
     * @param child PositionTable for the sub-element from start to end
     */
    public void setEnd(int end, PositionTable child) {
        endPos[currentEntry] = end;
        this.children[currentEntry] = child;
    }

    /**
     * Sets start in the position table for the next subterm to start.
     *
     * The number is determined by increment the counter of subterms by one.
     *
     * @param start char position that starts a sub-element
     */
    public void setStart(int start) {
        setStart(currentEntry + 1, start);
    }

    /**
     * Sets start in the position table for the subterm with the given number to start.
     *
     * @param subTermNo the 0-based number of the subterm to evaluate
     * @param start char position that starts a sub-element
     */
    public void setStart(int subTermNo, int start) {
        currentEntry = subTermNo;
        startPos[subTermNo] = start;
    }

    /**
     * Return of the children of this PositionTable
     */
    public PositionTable getChild(int i) {
        return children[i];
    }

    /**
     * returns a String representation of the position table
     */
    public String toString() {
        StringBuilder result = new StringBuilder("[");
        for (int i = 0; i < rows; i++) {
            result.append("<").append(startPos[i]).append(",").append(endPos[i]).append(",")
                    .append(children[i]).append(">");
            if (rows - 1 != i) {
                result.append(",");
            }
        }
        return result + "]";
    }

    /**
     * Returns a PosInSequent for a given position list, but without filling in the bounds. It is
     * assumed that this is a position table which has one child table for every formula in the
     * printed sequent, and that <code>posList</code> begins which the number of the formula. The
     * returned PosInSequent will refer to (a subterm of) one of the constrained formulae in the
     * sequent.
     *
     * @param posList the position list that navigates through the position tables.
     * @param filter the sequent print filter from that was used to print the sequent
     *
     * @return a PosInSequent for the given position list
     */

    protected PosInSequent getSequentPIS(ImmutableList<Integer> posList,
            SequentPrintFilter filter) {
        int cfmaNo = posList.head();
        ImmutableList<Integer> tail = posList.tail();

        SequentPrintFilterEntry filterEntry = getFilterEntry(cfmaNo, filter);

        // This can raise a NPE sporadically. (MU 19)
        // This raises an NPE repeatably (JS/MU 21) #1650
        SequentFormula cfma = filterEntry.getOriginalFormula();

        PosInOccurrence currentPos = new PosInOccurrence(cfma, PosInTerm.getTopLevel(),
            filter.getOriginalSequent().antecedent().contains(cfma));

        return children[cfmaNo].getTermPIS(filterEntry, tail, currentPos);
    }

    /**
     * Returns a PosInSequent for a given position list, but without filling in the bounds. It is
     * assumed that this is a position table corresponding to the Term <code>term</code>, which has
     * one child table for each subterm.
     *
     * @param filterEntry the print filter entry that contains information about which constrained
     *        formula we are in and how the constraint and metavariables were printed.
     * @param posList the position list that navigates through the position tables.
     * @param pio the PosInOccurrence leading to the current term
     */
    private PosInSequent getTermPIS(SequentPrintFilterEntry filterEntry,
            ImmutableList<Integer> posList, PosInOccurrence pio) {
        if (posList.isEmpty()) {
            return PosInSequent.createCfmaPos(pio);
        } else {
            int subNo = posList.head();
            PosInOccurrence subpio = pio.down(subNo);

            return children[subNo].getTermPIS(filterEntry, posList.tail(), subpio);
        }
    }

    private static SequentPrintFilterEntry getFilterEntry(int cfmaNo, SequentPrintFilter filter) {
        int i = cfmaNo;
        ImmutableList<SequentPrintFilterEntry> list =
            filter.getFilteredAntec().append(filter.getFilteredSucc());
        while (i-- != 0) {
            list = list.tail();
        }
        return list.head();
    }
}

// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.pp;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.IntIterator;
import de.uka.ilkd.key.logic.PosInOccurrence;

/**
 * An InitialPositionTable is a PositionTable that describes the
 * beginning of the element/subelement relationship. Thus, an
 * InitialPositionTable describes the information on where the
 * semisequents of a sequent are located. It is the root of the tree of
 * PositionTables and may be asked for a PosInSequent for a given index
 * position and a given Sequent.
 *
 * <p>For simplicity, the an InitialPositionTable has only one row.
 * The various constrained formulae of a sequent are located 
 * one level below.  In other words the whole sequent is not 
 * represented by an empty position list but by the list [0].
 */
public class InitialPositionTable extends PositionTable{

    private ImmutableList<Range> updateRanges = ImmutableSLList.<Range>nil();

    /**
     * creates a new Initial PositionTable.
     */
    public InitialPositionTable() {
	super(1);
    }

    /**
     * Returns the PosInSequent for a given char position in a 
     * sequent.
     * @param index the char position that points to the wanted
     *              position in sequent
     * @param filter the sequent print filter from that was used to
     *              print the sequent
     *
     */
    public PosInSequent getPosInSequent(int index,
					SequentPrintFilter filter) {
	if ( index < startPos[0] || index >= endPos[0]) {
	    return null;
	}

	ImmutableList<Integer> posList = pathForIndex(index);

	PosInSequent pis = getTopPIS(posList,filter);

	Range r = rangeForIndex(index);
	pis.setBounds(r);
	Range firstStatement 
	    = firstStatementRangeForIndex(index);
	if ( firstStatement!=null ) {
	    pis.setFirstJavaStatementRange(firstStatement);
	}
	return pis;
    }

    /** Returns a PosInSequent for a given position list, 
     * but without filling in the bounds.  It is assumed
     * that this is the top level position table for a sequent.
     * @param posList the position list that navigates through
     *                the position tables.
     * @param filter  the sequent print filter from that was used to
     *                print the sequent
     */
    private PosInSequent getTopPIS(ImmutableList<Integer> posList,
				   SequentPrintFilter filter) {
	if (posList.isEmpty() || posList.tail().isEmpty()) {
	    return PosInSequent.createSequentPos();	
	} else {
	    return child[0].getSequentPIS(posList.tail(),filter);
	}
    }


    /** Returns the path for a given PosInOccurrence.  This is 
     * built up from the initial 0, the number of the 
     * SequentFormula in the sequent, the position in the 
     * constrained formula, and possibly inside a Metavariable
     * instantiation. */
    public ImmutableList<Integer> pathForPosition(PosInOccurrence pio,
					 SequentPrintFilter filter) {
	ImmutableList<Integer> p = ImmutableSLList.<Integer>nil();

	p = prependPathInFormula(p,pio);
	p = p.prepend(Integer.valueOf(indexOfCfma(pio.constrainedFormula(),
					      filter)));
	p = p.prepend(Integer.valueOf(0));
	return p;
    }

    private ImmutableList<Integer> prependPathInFormula(ImmutableList<Integer> p,
					       PosInOccurrence pio) {
	IntIterator pit = pio.posInTerm().reverseIterator();
	while (pit.hasNext()) {
	    p = p.prepend(Integer.valueOf(pit.next()));
	}
	return p;
    }
    

    /** Returns the index of the constrained formula in the sequent
     * as printed. */
    private int indexOfCfma(SequentFormula cfma,
			    SequentPrintFilter filter) {
	ImmutableList<SequentPrintFilterEntry> list =
	    filter.getAntec().append(filter.getSucc());
	int k;
	for ( k=0 ; !list.isEmpty(); k++,list = list.tail() ) {
	    if (list.head().getOriginalFormula()==cfma) {
		return k;
	    }
	}
	return -1;
    }

    /**
     * Returns the character range of the `lowest' subtable that
     * includes <code>index</code> in its range.
     * @param index the character index to search for.
     */
    public Range rangeForIndex(int index) {
	return rangeForIndex(index,endPos[0]);
    }

    /** Returns the character range for the subtable indicated
     * by the given integer list.
     */
    public Range rangeForPath(ImmutableList<Integer> path) {
	return rangeForPath(path,endPos[0]);
    }

    public void addUpdateRange(Range r) {
        updateRanges = updateRanges.prepend(r);
    }

    public Range[] getUpdateRanges() {
        return updateRanges.toArray(new Range[updateRanges.size()]);
    }
}
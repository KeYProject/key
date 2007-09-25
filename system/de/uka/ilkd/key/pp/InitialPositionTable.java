// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.pp;

import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.Metavariable;
import de.uka.ilkd.key.util.Debug;

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

    private ListOfRange updateRanges = SLListOfRange.EMPTY_LIST;

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

	ListOfInteger posList = pathForIndex(index);

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
    private PosInSequent getTopPIS(ListOfInteger posList,
				   SequentPrintFilter filter) {
	if (posList.isEmpty() || posList.tail().isEmpty()) {
	    return PosInSequent.createSequentPos();	
	} else {
	    return child[0].getSequentPIS(posList.tail(),filter);
	}
    }


    /** Returns the path for a given PosInOccurrence.  This is 
     * built up from the initial 0, the number of the 
     * ConstrainedFormula in the sequent, the position in the 
     * constrained formula, and possibly inside a Metavariable
     * instantiation. */
    public ListOfInteger pathForPosition(PosInOccurrence pio,
					 SequentPrintFilter filter) {
	ListOfInteger p = SLListOfInteger.EMPTY_LIST;
	
	p = prependPathBelowMV(p,pio, entryForCfma(pio.constrainedFormula(),
	                                           filter));
	p = prependPathInFormula(p,pio);
	p = p.prepend(new Integer(indexOfCfma(pio.constrainedFormula(),
					      filter)));
	p = p.prepend(new Integer(0));
	return p;
    }

    private ListOfInteger prependPathBelowMV(ListOfInteger p,
                                             PosInOccurrence pio,
                                             SequentPrintFilterEntry entry) {
	if ( pio.posInTermBelowMetavariable () == null
             || !checkCompatibleDisplayConstraint ( pio, entry ) ) return p;

        IntIterator pit = pio.posInTermBelowMetavariable ().reverseIterator ();
        while ( pit.hasNext () ) {
            p = p.prepend ( new Integer ( pit.next () ) );
        }

        return p;
    }

    /**
     * Check that the term below the metavariable (as determined by the position
     * <code> pio </code> is compatible with the display constraint, i.e. with
     * the constraint that governs the shape of the current formula as
     * displayed. As it is possible to modify the user constraint arbitrarily,
     * this is not necessarily the case.
     * 
     * @return true iff the display constraint is compatible with
     *         <code>pio</code>
     */
    private boolean checkCompatibleDisplayConstraint (PosInOccurrence pio,
                                                      SequentPrintFilterEntry entry) {
        final Term mvTerm =
            pio.constrainedFormula ().formula ().subAt ( pio.posInTerm () );
        Debug.assertTrue ( mvTerm.op () instanceof Metavariable );
        final Metavariable mv = (Metavariable)mvTerm.op ();

        // The display constraint, joined with the statement that the focussed
        // metavariable is instantiated with the mounted term.
        final Constraint c = entry.getDisplayConstraint ()
            .unify ( mvTerm, pio.termBelowMetavariable (), null );
        if ( !c.isSatisfiable () ) return false;

        // the term that is displayed instead of the metavariable
        final Term displayedTerm = entry.getDisplayConstraint ().getInstantiation ( mv );
        // the term that ought to be displayed according to the term position
        final Term posTerm = c.getInstantiation ( mv );
        
        return posTerm.equals ( displayedTerm );
    }

    private ListOfInteger prependPathInFormula(ListOfInteger p,
					       PosInOccurrence pio) {
	IntIterator pit = pio.posInTerm().reverseIterator();
	while (pit.hasNext()) {
	    p = p.prepend(new Integer(pit.next()));
	}
	return p;
    }
    

    /** Returns the index of the constrained formula in the sequent
     * as printed. */
    private int indexOfCfma(ConstrainedFormula cfma,
			    SequentPrintFilter filter) {
	ListOfSequentPrintFilterEntry list =
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
     * Returns the <code>SequentPrintFilterEntry</code> for the given
     * constrained formula from the <code>filter</code>.
     */
    private SequentPrintFilterEntry entryForCfma (ConstrainedFormula cfma,
                                                  SequentPrintFilter filter) {
        ListOfSequentPrintFilterEntry list =
            filter.getAntec ().append ( filter.getSucc () );
        int k;
        for ( k = 0; !list.isEmpty (); k++, list = list.tail () ) {
            if ( list.head ().getOriginalFormula () == cfma ) {
                return list.head ();
            }
        }
        return null;
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
    public Range rangeForPath(ListOfInteger path) {
	return rangeForPath(path,endPos[0]);
    }

    public void addUpdateRange(Range r) {
        updateRanges = updateRanges.prepend(r);
    }

    public Range[] getUpdateRanges() {
        return updateRanges.toArray();
    }

}



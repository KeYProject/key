// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
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

/**
 * A PositionTable describes the start and end positions of substrings
 * of a String in order to get a PosInSequent from an int describing a
 * position in a string representing a Term or a Sequent, etc. A
 * PositionTable therefore represents a table consisting of two
 * columns of type int (start and end position) and a reference to
 * another PositionTable representing the position information for
 * that substring.  A PositionTable is valid (in order to support
 * efficient putting of new entries to the table and an efficient
 * search for a Position), if the last entry that has been set is (s,
 * e, x) and the next entry is (s', e', x') with s'>e.
 * 
 * <p>Positions are reckoned with start positions inclusive and
 * end positions exclusive.  Start and end positions are relative
 * to each subterm.
 */
public class PositionTable {

    // the start positions of the direct subterms (or parts of sequent, etc.)
    protected int[] startPos;

    //the end positions of the direct subterms (or parts of sequent, etc.)   
    protected int[] endPos;

    // the PositionTables for the direct subterms (or parts of sequent, etc.)
    protected PositionTable[] child;    

    // the entry number where the next entry in endPos will be set
    private int currentEndEntry=0;

    // the entry number where the next entry in startPos will be set
    private int currentStartEntry=0;

    // the number of rows in the above arrays. Equals the number of direct 
    // subterms (or parts of sequent, etc.)
    private final int rows;

    /**
     * creates a new PositionTable with the number of subterms (or number of
     * ConstrainedFormula in a Semisequent, or the number of Semisequents in a
     * Sequent, etc.)
     * @param rows the number of direct sub-elements in the term whose
     * position information is represented by the constructed object.
     */
    public PositionTable(int rows) {
	this.rows=rows;
	startPos=new int[rows];
	endPos=new int[rows];
	child=new PositionTable[rows];
	for (int i=0; i<rows; i++) {
	    startPos[i]=-1;
	    endPos[i]=-1;
	    child[i]=null;
	}
    }

    /**
     * returns the m with startPos[m]<=index<=endPos[m]. 
     * -1 if no such m exists.
     */
    private int searchEntry(int index) {

	//linear search:
	for (int m=0; m<rows; m++) {
	    if ((startPos[m]<=index) && (index < endPos[m])) {
		return m;
	    }
	}


	//binary search (ordered arrays are precondition!), NOT CHECKED SO FAR:
/*	int l=0;
	int r=rows-1;
	int m;
	while (r<l) { 
	    m=(l+r)/2; 
	    if ((startPos[m]<=index) && (endPos[m]>index)) {
		return m; 
	    } 
	    if (index<startPos[m]) {
		r=m; 
	    } else { 
		l=m; 
	    }
	    }*/
	return -1;
    }

    /**
     * Returns the path to the `lowest' position table that includes
     * <code>index</code> in its range.
     */
    protected ListOfInteger pathForIndex(int index) {
	int sub=searchEntry(index);
	if (sub == -1) {
	    return SLListOfInteger.EMPTY_LIST;
	} else {
	    return child[sub].pathForIndex(index-startPos[sub])
		.prepend(new Integer(sub));
	}
    }

    /**
     * Returns the character range of the `lowest' subtable that
     * includes <code>index</code> in its range.
     * @param index the character index to search for.
     * @param length the length of the whole string corresponding
     *              to this position table.  Needed in case it
     *              turns out the index belongs to the top level.
     */
    public Range rangeForIndex(int index,int length) {
	int sub=searchEntry(index);
	if (sub==-1) {
	    return new Range(0,length);
	} else {
	    Range r = child[sub].rangeForIndex(index-startPos[sub],
					       endPos[sub]-startPos[sub]);
	    r.start += startPos[sub];
	    r.end   += startPos[sub];
	    return r;
	}
    }

    /**
     * Returns the character range of the first java statement in a
     * program modality for the `lowest' subtable that includes
     * <code>index</code> in its range.  If the lowest subtable
     * does not correspond to a program modality, it returns null.
     */
    public Range firstStatementRangeForIndex(int index) {
	int sub=searchEntry(index);
	if (sub==-1) {
	    return getFirstStatementRange();
	} else {
	    Range r = child[sub].
		firstStatementRangeForIndex(index-startPos[sub]);
	    if (r!=null) {
		r.start += startPos[sub];
		r.end   += startPos[sub];
	    }
	    return r;
	}
    }
    
    /** Returns the character range of the first java statement in a
     * program modality for <i>this</i>position table.  If this
     * is not a program modality, returns null.  Note that this
     * will be overridden in the subclass 
     * {@link ModalityPositionTable}.
     */
    public Range getFirstStatementRange(){
	return null;
    }


    /** Returns the character range for the subtable indicated
     * by the given integer list.
     */
    public Range rangeForPath(ListOfInteger path,int length) {
	if (path.isEmpty()) {
	    return new Range(0,length);
	} else {
	    int sub = path.head().intValue();
	    Range r = child[sub].rangeForPath(path.tail(),
					      endPos[sub]-startPos[sub]);
	    r.start += startPos[sub];
	    r.end   += startPos[sub];
	    return r;	    
	}
    }



    /**
     * sets end in the position table to the next free end entry in the 
     * position
     * table and sets the given PositionTable as child of the sub-element
     * finished by putting this end position
     * @param end char position that ends the sub-element started by the 
     * corresponding start entry in the position table
     * @param child PositionTable for the sub-element from start to end
     */
    public void setEnd(int end, PositionTable child) {
	endPos[currentEndEntry]=end;
	this.child[currentEndEntry]=child;
	currentEndEntry++;
    }

    /**
     * sets start in the position table to the next free start entry in the 
     * position table 
     * @param start char position that starts a sub-element
     */
    public void setStart(int start) {
	startPos[currentStartEntry]=start;
	currentStartEntry++;
    }

    /**
     * Return of the children of this PositionTable
     */
    public PositionTable getChild(int i) {
	
	return child[i];
    }

    /**
     * returns a String representation of the position table
     */
    public String toString() {
	String result="[";
	for (int i=0; i<rows; i++) {
	    result=result+"<"+startPos[i]+","+endPos[i]+","+child[i]+">";
	    if (rows-1!=i) result=result+",";
	}
	return result+"]";
    }


    /** Returns a PosInSequent for a given position list, 
     * but without filling in the bounds.  It is assumed
     * that this is a position table which has one child table for
     * every formula in the printed sequent, and that
     * <code>posList</code> begins which the number of the formula.
     * The returned PosInSequent will refer to (a subterm of) one 
     * of the constrained formulae in the sequent.
     * @param posList the position list that navigates through
     *                the position tables.
     * @param filter  the sequent print filter from that was used to
     *                print the sequent
     */    
    
    protected PosInSequent getSequentPIS(ListOfInteger posList,
				       SequentPrintFilter filter) {
	int cfmaNo = posList.head().intValue();
	ListOfInteger tail = posList.tail();

	SequentPrintFilterEntry filterEntry = 
	    getFilterEntry(cfmaNo, filter);

	ConstrainedFormula cfma = filterEntry.getOriginalFormula();

	PosInOccurrence currentPos = 
	    new PosInOccurrence ( cfma, PosInTerm.TOP_LEVEL,
				  filter.getSequent ().antecedent().contains(cfma) );
	
	return child[cfmaNo].getTermPIS(filterEntry,tail,
					currentPos);
    }
    

    /** Returns a PosInSequent for a given position list, but without
     * filling in the bounds.  It is assumed that this is a position
     * table corresponding to the Term <code>term</code>, which has
     * one child table for each subterm.
     * @param filterEntry the print filter entry that contains
     *                information about which constrained formula we
     *                are in and how the constraint and metavariables
     *                were printed.
     * @param posList the position list that navigates through
     *                the position tables.
     * @param pio     the PosInOccurrence leading to the current term
     */
    private PosInSequent getTermPIS(SequentPrintFilterEntry filterEntry,
				    ListOfInteger posList,
				    PosInOccurrence pio) {
	if(posList.isEmpty()) {
	    return PosInSequent.createCfmaPos(pio);
	} else {
	    int subNo  =  posList.head().intValue();
	    PosInOccurrence subpio = pio.down ( subNo );
	    Term subterm = subpio.subTerm();

	    if ( subpio.termBelowMetavariable() == null &&
		 subterm.op() instanceof Metavariable ) {
		subpio = goInMetavariable((Metavariable)subterm.op(),
					  filterEntry,
					  subpio);
	    }
	    return child[subNo].getTermPIS(filterEntry,
					   posList.tail(),
					   subpio);
	}
    }
    
    /** Handles the special case for <code>getTermPIS()</code> when
     * the position moves below a Metavariable.  The SequentPrintFilter
     * can replace Metavariables by their instantiation according to
     * the user constraint.  When the user selects a position
     * inside such an instantiation, this needs to be recorded.
     * @param mv      a Metavariable
     * @param filterEntry the print filter entry that contains
     *                information about which constrained formula we
     *                are in and how the constraint and metavariables
     *                were printed.
     * @param pos     the PosInOccurrence leading to the meta variable
     * @returns  the PosInOccurrence with the added information that
     *           we are inside a MV instantiation.
     */
    private PosInOccurrence goInMetavariable(
 			       Metavariable mv,
                               SequentPrintFilterEntry filterEntry,
			       PosInOccurrence pos) {
	Term t = filterEntry
	    .getDisplayConstraint()
	    .getInstantiation(mv);
	if ( t.op() != mv ) {
	    return pos.setTermBelowMetavariable(t);
	} else {
	    return pos;
	}
    }


    private static SequentPrintFilterEntry 
	getFilterEntry(int cfmaNo, 
		       SequentPrintFilter filter) {
	int i = cfmaNo;
	ListOfSequentPrintFilterEntry list =
	    filter.getAntec().append(filter.getSucc());
	while ( i-- != 0 ) list = list.tail ();
	return list.head ();
    }




}



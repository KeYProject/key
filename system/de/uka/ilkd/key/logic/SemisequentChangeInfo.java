// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//


package de.uka.ilkd.key.logic;

/**
 * Records the changes made to a semisequent. Keeps track of added and
 * removed formula to the semisequents. 
 */
public class SemisequentChangeInfo implements java.io.Serializable {
    
    /** contains the added formulas to the semisequent */
    private ListOfConstrainedFormula added   = SLListOfConstrainedFormula.EMPTY_LIST;
    /** contains the removed formulas from the semisequent */
    private ListOfConstrainedFormula removed = SLListOfConstrainedFormula.EMPTY_LIST;
    /** contains the modified formulas from the semisequent */
    private ListOfFormulaChangeInfo modified = SLListOfFormulaChangeInfo.EMPTY_LIST;
    /** stores the redundance free formula list of the semisequent */
    private ListOfConstrainedFormula modifiedSemisequent =
	SLListOfConstrainedFormula.EMPTY_LIST; 
    /**
     * contains formulas that have been tried to add, but which have been rejected due to
     * already existing formulas in the sequent subsuming these formulas 
     */
    public ListOfConstrainedFormula rejected = SLListOfConstrainedFormula.EMPTY_LIST; 
    
    /** */
    private int lastFormulaIndex = -1;
    
    /** the resulting semisequent */
    private Semisequent semisequent;   
    

    public SemisequentChangeInfo() {
    }

    public SemisequentChangeInfo(ListOfConstrainedFormula formulas) {
      this.modifiedSemisequent = formulas;
    }

    /** 
     * returns true if the semisequent has changed
     */
    public boolean hasChanged() {
	return !added.isEmpty() || 
	       !removed.isEmpty() ||
	       !modified.isEmpty();
    }

    /**
     * sets the list of constrained formula containing all formulas of
     * the semisequent after the operation
     */
    public void setFormulaList(ListOfConstrainedFormula list) {
	modifiedSemisequent = list;
    }

    /**
     * returns the list of constrained formula of the new semisequent
     */
    public ListOfConstrainedFormula getFormulaList() {
	return modifiedSemisequent;
    }
    
    /** 
     * logs an added formula at position idx
     */
    public void addedFormula(int idx, ConstrainedFormula cf) {
	added = added.prepend(cf);
	lastFormulaIndex = idx;
    }

    /** 
     * logs a modified formula at position idx
     */
    public void modifiedFormula(int idx,
				FormulaChangeInfo fci) {
	// This information can overwrite older records about removed
	// formulas
	removed  = removed.removeAll
	    ( fci.getPositionOfModification ().constrainedFormula () );
	modified = modified.prepend ( fci );
	lastFormulaIndex = idx;
    }

    /** 
     * returns the list of all added constrained formulas
     * @return ListOfConstrainedFormula added to the semisequent
     */
    public ListOfConstrainedFormula addedFormulas() {
	return added;
    }

    /** 
     * returns the list of all removed constrained formulas
     * @return ListOfConstrainedFormula removed from the semisequent
     */
    public ListOfConstrainedFormula removedFormulas() {
	return removed;
    }
    
    /**
     * returns a list of formulas that have been tried to add to 
     * the semisequent but got rejected as they were redundant
     * @return list of formulas rejected due to redundancy
     */
    public ListOfConstrainedFormula rejectedFormulas() {
        return this.rejected;
    }
    
 
    /**
     * adding formula <tt>f</tt> to the semisequent failed due to 
     * a redundance check. This means an equal or stronger formula
     * is already present in the semisequent 
     * @param f the ConstrainedFormula  
     */
    public void rejectedFormula(ConstrainedFormula f) {
       this.rejected = this.rejected.append(f);
    }

    /** 
     * returns the list of all modification positions
     * @return ListOfConstrainedFormula modified within the
     * semisequent
     */
    public ListOfFormulaChangeInfo modifiedFormulas() {
	return modified;
    }    

    /** 
     * logs an added formula at position idx
     */
    public void removedFormula(int idx, ConstrainedFormula cf) {
	removed = removed.prepend(cf);

	lastFormulaIndex = ( lastFormulaIndex == idx ) ? -1 :
	    lastFormulaIndex > idx ? lastFormulaIndex - 1 : lastFormulaIndex;

	if (lastFormulaIndex < -1) {
	    lastFormulaIndex = -1;
	}
	
    }

    /**
     * returns the index of the last added formula
     */
    public int getIndex() {
	return lastFormulaIndex;
    }

    /** 
     * sets the resulting semisequent
     */
    public void setSemisequent(Semisequent semisequent) {
	this.semisequent = semisequent;
    }
    
    /** 
     * returns the semisequent that is the result of the change
     * operation
     */
    public Semisequent semisequent() {
	return semisequent;
    }


    /**
     * toString
     */
    public String toString() {
	return "changed:"+hasChanged()+
	    "\n  added (pos):"+added+"("+lastFormulaIndex+")"+
	    "\n  removed:"+removed+
	    "\n  modified:"+modified+
            "\n  rejected:"+rejected +
	    "\n  new semisequent:"+modifiedSemisequent;
    }

}

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

package de.uka.ilkd.key.logic;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;

/**
 * Records the changes made to a semisequent. Keeps track of added and
 * removed formula to the semisequents. 
 */
public class SemisequentChangeInfo {
    
    /** contains the added formulas to the semisequent */
    private ImmutableList<SequentFormula> added   = ImmutableSLList.<SequentFormula>nil();
    /** contains the removed formulas from the semisequent */
    private ImmutableList<SequentFormula> removed = ImmutableSLList.<SequentFormula>nil();
    /** contains the modified formulas from the semisequent */
    private ImmutableList<FormulaChangeInfo> modified = ImmutableSLList.<FormulaChangeInfo>nil();
    /** stores the redundance free formula list of the semisequent */
    private ImmutableList<SequentFormula> modifiedSemisequent =
	ImmutableSLList.<SequentFormula>nil(); 
    /**
     * contains formulas that have been tried to add, but which have been rejected due to
     * already existing formulas in the sequent subsuming these formulas 
     */
    public ImmutableList<SequentFormula> rejected = ImmutableSLList.<SequentFormula>nil(); 
    
    /** */
    private int lastFormulaIndex = -1;
    
    /** the resulting semisequent */
    private Semisequent semisequent;   
    

    public SemisequentChangeInfo() {
    }

    public SemisequentChangeInfo(ImmutableList<SequentFormula> formulas) {
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
    public void setFormulaList(ImmutableList<SequentFormula> list) {
	modifiedSemisequent = list;
    }

    /**
     * returns the list of constrained formula of the new semisequent
     */
    public ImmutableList<SequentFormula> getFormulaList() {
	return modifiedSemisequent;
    }
    
    /** 
     * logs an added formula at position idx
     */
    public void addedFormula(int idx, SequentFormula cf) {
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
     * @return IList<SequentFormula> added to the semisequent
     */
    public ImmutableList<SequentFormula> addedFormulas() {
	return added;
    }

    /** 
     * returns the list of all removed constrained formulas
     * @return IList<SequentFormula> removed from the semisequent
     */
    public ImmutableList<SequentFormula> removedFormulas() {
	return removed;
    }
    
    /**
     * returns a list of formulas that have been tried to add to 
     * the semisequent but got rejected as they were redundant
     * @return list of formulas rejected due to redundancy
     */
    public ImmutableList<SequentFormula> rejectedFormulas() {
        return this.rejected;
    }
    
 
    /**
     * adding formula <tt>f</tt> to the semisequent failed due to 
     * a redundance check. This means an equal or stronger formula
     * is already present in the semisequent 
     * @param f the SequentFormula  
     */
    public void rejectedFormula(SequentFormula f) {
       this.rejected = this.rejected.append(f);
    }

    /** 
     * returns the list of all modification positions
     * @return IList<SequentFormula> modified within the
     * semisequent
     */
    public ImmutableList<FormulaChangeInfo> modifiedFormulas() {
	return modified;
    }    

    /** 
     * logs an added formula at position idx
     */
    public void removedFormula(int idx, SequentFormula cf) {
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
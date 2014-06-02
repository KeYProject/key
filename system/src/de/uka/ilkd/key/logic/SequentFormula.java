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

import de.uka.ilkd.key.logic.sort.Sort;


/** 
 * A sequent formula is a wrapper around a formula that occurs 
 * as top level formula in a sequent. SequentFormula instances have
 * to be unique in the sequent as they are used by PosInOccurrence 
 * to determine the exact position. In earlier KeY versions this class 
 * was called ConstrainedFormula as it was equipped with an additional 
 * constraints. It would be interesting to add more value to this class 
 * by providing a way to add additional annotations or to cache local information 
 * about the formula.
 */
public class SequentFormula {

    private final Term term;
   
    private final int hashCode;
    
    /** creates a new SequentFormula 
     * @param term a Term of sort Sort.FORMULA
     */ 
    public SequentFormula(Term term) {
	if (term.sort() != Sort.FORMULA) {
	    throw new RuntimeException("A Term instead of a formula: " + term);
	}
	this.term = term;	
	this.hashCode = term.hashCode () * 13;
    }

    /** @return the stored Term */
    public Term formula() {
	return term;
    }

    /** equal if terms and constraints are equal */
    public boolean equals(Object obj) {
        if (this == obj) { return true; }
	if (obj instanceof SequentFormula) {
	    SequentFormula cmp=(SequentFormula)obj;
	    if (term.equals(cmp.formula())) {
		return true;
	    }
	}
	return false;
    }

    /** String representation */
    public String toString() {
	return term.toString();
    }
    
    public int hashCode () {
        return hashCode;
    }
}
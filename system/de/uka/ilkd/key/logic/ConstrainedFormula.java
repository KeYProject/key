// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.logic;

import de.uka.ilkd.key.logic.sort.Sort;


/** This class contains a term of type bool with the constraints it
 * has to satisfy. In opposition to terms a ConstrainedFormula is not
 * persistent.
 */
public class ConstrainedFormula {

    private final Term term;
   

    private final int hashCode;
    
    /** creates a new ConstrainedFormula 
     * @param term a Term of sort Sort.FORMULA
     */ 
    public ConstrainedFormula(Term term) {
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
	if (obj instanceof ConstrainedFormula) {
	    ConstrainedFormula cmp=(ConstrainedFormula)obj;
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

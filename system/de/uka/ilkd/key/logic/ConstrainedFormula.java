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

import de.uka.ilkd.key.logic.sort.Sort;


/** This class contains a term of type bool with the constraints it
 * has to satisfy. In opposition to terms a ConstrainedFormula is not
 * persistent.
 */
public class ConstrainedFormula implements java.io.Serializable {

    private final Term term;
    private final Constraint constraint;

    private final int hashCode;
    
    /** creates a new ConstrainedFormula 
     * @param term a Term of sort Sort.FORMULA
     * @param constraint the Contraint that has to be satisfied 
     */ 
    public ConstrainedFormula(Term term, Constraint constraint) {
	if (term.sort() != Sort.FORMULA) {
	    throw new RuntimeException("A Term instead of a Formula");
	}
	this.term = term;	
	this.constraint = constraint;
	this.hashCode = term.hashCode () * 13 + constraint.hashCode ();
    }

    /** creates a new ConstrainedFormula with the `empty' constraint
     * BOTTOM.
     * @param term a Term of sort Sort.FORMULA
     */ 
    public ConstrainedFormula(Term term) {
	this(term,Constraint.BOTTOM);
    }

    /** @return the stored Term */
    public Term formula() {
	return term;
    }

    /** @return the stored Constraint */
    public Constraint constraint() {
	return constraint;
    }

    /** equal if terms and constraints are equal */
    public boolean equals(Object obj) {
        if (this == obj) { return true; }
	if (obj instanceof ConstrainedFormula) {
	    ConstrainedFormula cmp=(ConstrainedFormula)obj;
	    if (term.equals(cmp.formula()) && constraint.equals(cmp.constraint())) {
		return true;
	    }
	}
	return false;
    }

    /** String representation */
    public String toString() {
	return term+
	    (constraint.isBottom() ? "" : "<<"+constraint);
    }
    
    public int hashCode () {
        return hashCode;
    }
}

// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.sort.Sort;

class TermSV extends AbstractTermSV {

    /**
     * this flag indicates if the instantiation of this schemavariable must have
     * the same static type (sort) as this SV itself
     */
    private final boolean strictSV;

    /** creates a new SchemaVariable. That is used as placeholder for
     * terms.
     * @param name the Name of the SchemaVariable
     * @param sort the Sort of the SchemaVariable and the matched type     
     * @param listSV a boolean which is true iff the schemavariable is allowed
     * to match a list of terms    
     * @param rigidness true iff this SV may only match rigid
     * terms/formulas
     * @param strictSV boolean indicating if the schemavariable is declared as strict
     * forcing exact type match
     */    
    TermSV(Name    name,
		   Sort    sort,
		   boolean listSV,
		   boolean rigidness, 
                   boolean strictSV) {	
        super(name, sort, listSV, rigidness);
        this.strictSV = strictSV;
	if (sort == Sort.FORMULA) {
	    throw new RuntimeException("A TermSV is not allowed to"
				       +" have the sort "+sort);
	}	
    }
	
    
    /** returns true iff this SchemaVariable is used to match
     * a term but not a formula
     * @return true iff this SchemaVariable is used to match
     * a term but not a formula
     */
    public boolean isTermSV() {
	return true;
    }
	
    /**
     * @return true if the schemavariable has the strict modifier 
     * which forces the instantiation to have exact the same sort
     * as the schemavariable (or if the sv is of generic sort - 
     * the instantiation of the generic sort)
     */
    public boolean isStrict () {
        return strictSV;
    }
    
    /** toString */
    public String toString() {
        return toString(sort().toString()+" term");
    }
}

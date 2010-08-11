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

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.MatchConditions;

class SkolemTermSV extends SortedSchemaVariable {

    /** 
     * creates a new SchemaVariable. That is used as placeholder for
     * skolem terms.
     * @param name the Name of the SchemaVariable
     * @param sort the Sort of the SchemaVariable and the matched type     
     * @param listSV a boolean which is true iff the schemavariable is
     * allowed to match a list of program constructs
     */    
    SkolemTermSV(Name name, Sort sort, boolean listSV) {
	super(name, Term.class, sort, listSV);	
	if (sort == Sort.FORMULA) {
	    throw new RuntimeException("A SkolemTermSV is not allowed to"
				       +" have the sort "+sort);
	}
	
    }
	
    /** returns true iff this SchemaVariable is used to match
     * a term but not a formula
     * @return true iff this SchemaVariable is used to match
     * a term but not a formula
     */
    public boolean isSkolemTermSV() {
	return true;
    }
    
    public boolean isRigid () {
	return true;
    }

    /** toString */
    public String toString() {
	return toString(sort().toString()+" skolem term");
    }


    /*    
     * @see de.uka.ilkd.key.logic.op.SortedSchemaVariable#match(de.uka.ilkd.key.logic.op.SVSubstitute, de.uka.ilkd.key.rule.MatchConditions, de.uka.ilkd.key.java.Services)
     */
    public MatchConditions match(SVSubstitute subst, MatchConditions mc, Services services) {        
        return null;
    }
	
}

// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.Sort;

abstract class AbstractTermSV extends SortedSchemaVariable {
    
    private final boolean rigidness;
    
    /** creates a new SchemaVariable
     * @param name the Name of the SchemaVariable
     * @param sort the Sort of the SchemaVariable and the matched type     
     * @param listSV a boolean which is true iff the schemavariable is allowed
     * to match a list of terms
     * @param rigidness true iff this SV may only match rigid
     * terms/formulas
     */    
    AbstractTermSV(Name    name,
            Sort    sort,
            boolean listSV,
            boolean rigidness) {
	super(name, Term.class, sort, listSV);
	this.rigidness = rigidness;
    }
	
    /**
     * @return true if the value of "term" having this operator as
     * top-level operator and may not be changed by modalities
     */
    public boolean isRigid () {
	return rigidness;
    }  
}

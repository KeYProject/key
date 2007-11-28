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
import de.uka.ilkd.key.logic.sort.Sort;

class FormulaSV extends AbstractTermSV {
    /** creates a new SchemaVariable. That is used as placeholder for
     * formulae.
     * @param name the Name of the SchemaVariable
     * @param rigidness true iff this SV may only match rigid
     * terms/formulas
     * @param listSV a boolean which is true iff the schemavariable is allowed
     * to match a list of formulas
     */    
    FormulaSV(Name name, boolean listSV, boolean rigidness) {
	super(name, Sort.FORMULA, listSV, rigidness);
    }
    
    /** 
     * returns true iff this SchemaVariable is used to match
     * a formula 
     * @return true iff this SchemaVariable is used to match
     * a formula
     */
    public boolean isFormulaSV() {
	return true;
    }    
    
    /** toString */
    public String toString() {
	return toString("formula");
    }	
}

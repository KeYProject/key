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

package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.sort.Sort;


/** 
 * A schema variable that is used as placeholder for formulas.
 */  
public final class FormulaSV extends AbstractSV {
    
    /** 
     * @param name the name of the SchemaVariable
     * @param isRigid true iff this SV may only match rigid formulas
     */
    FormulaSV(Name name, boolean isRigid) {
	super(name, Sort.FORMULA, isRigid, true);
    }
    
    @Override
    public String toString() {
	return toString("formula");
    }	
    
    
    @Override
    public String proofToString() {
	return "\\schemaVar \\formula " + name() + ";\n";
    }
}
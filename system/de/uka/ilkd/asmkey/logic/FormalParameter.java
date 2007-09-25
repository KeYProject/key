// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.asmkey.logic;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.sort.Sort;


/** Formal parameters of named asm rules. Instances of this class
 * represents formal parameters in named asm rules. They are similar
 * to logical variables, but may only occur in definitions of named
 * asm rules.  Formal parameters are replaced with concrete arguments
 * on rule invocation (inlining). */

public final class FormalParameter extends AsmOp {

    /** creates a new formal parameter with the given name and given
     * sort. */
    FormalParameter(Name id, Sort sort) {
        super(id, sort);
    }

    /** create a new formal parameter
     */
    public static FormalParameter createFormalParameter(String id, Sort sort) {
	assert id!=null && sort!= null:"FormalParameter instances do not accept null values";
	return new FormalParameter(new Name(id), sort);
    }

    public static Sort[] parametersAsSort(FormalParameter[] params) {
	Sort[] args = new Sort[params.length];
	for(int i = 0; i< args.length; i++) {
	    args[i] = params[i].sort();
	}
	return args;
    }

}

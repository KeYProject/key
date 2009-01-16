// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//

package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.abstraction.ListOfKeYJavaType;
import de.uka.ilkd.key.java.statement.MethodBodyStatement;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.op.*;


/** 
 * Symbolically executes a method invocation
 */ 
public class MethodCallContract extends MethodCall {


    /** creates the methodcall-MetaConstruct 
     * @param result the SchemaVariable that is used to keep the result
     * @param body the ProgramElement contained by the meta construct 
     */
    public MethodCallContract(ProgramSV ec, SchemaVariable result,
		      ProgramElement body) {
	super(new Name("method-call-contract"), ec, result, body);
    }

    protected Statement makeIfCascade(ListOfKeYJavaType imps, Services services) {        
        ProgramMethod meth = getMethod(staticPrefixType, methRef, services);
        return new MethodBodyStatement(meth, newContext,
                                       pvar, arguments, true, methRef.getScope()); 
    }


}

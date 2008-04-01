// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.expression.literal.BooleanLiteral;
import de.uka.ilkd.key.java.recoderext.ImplicitFieldAdder;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * creates an assignment instantiationOf(#newObjectsV).<initialized> = true
 */
public class PostWork extends ProgramMetaConstruct {
    
    
     /** creates a typeof ProgramMetaConstruct 
     * @param newObjectSV the instance of expression contained by 
     * the meta construct 
     */
    public PostWork(SchemaVariable newObjectSV) {
	super("post-work", (Expression)newObjectSV); 
    }

    /** 
     * performs the program transformation needed for symbolic
     * program transformation 
     * @return the transformated program
     */
    public ProgramElement symbolicExecution(ProgramElement pe,
					    Services services,
					    SVInstantiations svInst) {       
	final ProgramVariable newObject = 
	    (ProgramVariable) svInst.getInstantiation((SchemaVariable)body());

	final ProgramVariable initialized = services.getJavaInfo().getAttribute
	    (ImplicitFieldAdder.IMPLICIT_INITIALIZED,  
             services.getJavaInfo().getJavaLangObject());
	return assign(attribute(newObject, initialized), BooleanLiteral.TRUE);
    }
}

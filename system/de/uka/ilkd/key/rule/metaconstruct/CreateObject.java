// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2004 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.java.ArrayOfExpression;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.declaration.ClassDeclaration;
import de.uka.ilkd.key.java.expression.operator.New;
import de.uka.ilkd.key.java.recoderext.CreateObjectBuilder;
import de.uka.ilkd.key.java.reference.MethodReference;
import de.uka.ilkd.key.java.reference.TypeReference;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.rule.inst.SVInstantiations;


/**
 * If an allocation expression <code>new Class(...)</code> occurs, a new object
 * has to be created, in KeY this is quite similar to take it out of a list of
 * objects and setting the implicit flag <code> &lt;created&gt; </code> to
 * <code>true</code> as well as setting all fields of the object to their
 * default values. For the complete procedure, the method creates the 
 * implicit method <code>&lt;createObject&gt;</code> which on its part calls
 * another implicit method <code>lt;prepare&gt;</code> for setting the fields
 * values.
 */
public class CreateObject extends ProgramMetaConstruct {

    public CreateObject(ProgramElement newExpr) {	
	super("create-object", newExpr); 
    }


    /**
     * creates and returns a method reference to the implicit '<createObject>'
     * method 
     */
    public ProgramElement symbolicExecution(ProgramElement pe, 
					    Services services,
					    SVInstantiations svInst) {
	
 	TypeReference classReference = ((New)pe).getTypeReference();

  	if (!(classReference.getKeYJavaType().getJavaType() 
	      instanceof ClassDeclaration)) {
  	    // no implementation available
  	    return pe;
  	}	
 	
        return new MethodReference(new ArrayOfExpression(), 
				   new ProgramElementName
                                   (CreateObjectBuilder.IMPLICIT_OBJECT_CREATE), 
				   classReference);					   
    }
}

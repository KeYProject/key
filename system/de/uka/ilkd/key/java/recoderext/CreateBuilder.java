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
package de.uka.ilkd.key.java.recoderext;

import recoder.CrossReferenceServiceConfiguration;
import recoder.java.Identifier;
import recoder.java.StatementBlock;
import recoder.java.declaration.ClassDeclaration;
import recoder.java.declaration.MethodDeclaration;
import recoder.java.declaration.TypeDeclaration;
import recoder.java.declaration.modifier.Private;
import recoder.java.expression.literal.BooleanLiteral;
import recoder.java.expression.literal.IntLiteral;
import recoder.java.reference.MethodReference;
import recoder.java.reference.ThisReference;
import recoder.java.reference.TypeReference;
import recoder.java.statement.Return;
import recoder.list.*;

/**
 * If an allocation expression <code>new Class(...)</code> occurs, a new object
 * has to be created, in KeY this is quite similar to take it out of a list of
 * objects and setting the implicit flag <code> &lt;created&gt; </code> to
 * <code>true</code> as well as setting all fields of the object to their
 * default values. For the complete procedure, the method creates the 
 * implicit method <code>&lt;createObject$gt;</code> which on its part calls
 * another implicit method <code>lt;prepare&gt;</code> for setting the fields
 * default values.
 */
public class CreateBuilder extends RecoderModelTransformer {

    public static final String IMPLICIT_CREATE = "<create>";

    public CreateBuilder
	(CrossReferenceServiceConfiguration services, 
	 CompilationUnitMutableList units) {	
	super(services, units);
    }


    /** 
     * Creates the body of the static <code>&lt;createObject&gt;</code>
     * method.
     */
    private StatementBlock createBody(ClassDeclaration recoderClass) {
		
	StatementMutableList result = new StatementArrayList(10);

	
	result.add
	    (assign(attribute(new ThisReference(), 
			      new ImplicitIdentifier
			      (ImplicitFieldAdder.IMPLICIT_TRANSIENT)),
		    new IntLiteral(0)));


	result.add
	    (assign(attribute(new ThisReference(), 
			      new ImplicitIdentifier
			      (ImplicitFieldAdder.IMPLICIT_INITIALIZED)),
		    new BooleanLiteral(false)));       


	result.add
	    (new MethodReference(null,
				 new ImplicitIdentifier
				 (PrepareObjectBuilder.IMPLICIT_OBJECT_PREPARE_ENTER)));

	result.add(new Return(new ThisReference()));

	return new StatementBlock(result);
	
    }
    

    /**
     * creates the implicit static <code>&lt;createObject&gt;</code>
     * method that takes the object to be created out of the pool
     * @param type the TypeDeclaration for which the
     * <code>&lt;prepare&gt;</code> is created
     * @return the implicit <code>&lt;prepare&gt;</code> method
     */
    public MethodDeclaration createMethod(ClassDeclaration type) {
	ModifierMutableList modifiers = new ModifierArrayList(2);
	modifiers.add(new Private());
	MethodDeclaration md =  new MethodDeclaration
	    (modifiers, 
	     new TypeReference
	     ((Identifier)type.getIdentifier().deepClone()), 
	     new ImplicitIdentifier(IMPLICIT_CREATE), 
	     new ParameterDeclarationArrayList(0), 
	     null,
	     createBody(type));
	md.makeAllParentRolesValid();
	return md;
    }    


    /**
     * entry method for the constructor normalform builder
     * @param td the TypeDeclaration 
     */
    protected void makeExplicit(TypeDeclaration td) {
	if (td instanceof ClassDeclaration) {
	    attach(createMethod((ClassDeclaration)td), 
		   td, td.getMembers().size());
//  	    java.io.StringWriter sw = new java.io.StringWriter();
//  	    services.getProgramFactory().getPrettyPrinter(sw).visitClassDeclaration((ClassDeclaration)td);
//  	    System.out.println(sw.toString());
//  	    try { sw.close(); } catch (Exception e) {}		
	}
    }






}

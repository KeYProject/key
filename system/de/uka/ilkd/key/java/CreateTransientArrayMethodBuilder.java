// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.java;

import java.util.LinkedList;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.java.abstraction.Field;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.*;
import de.uka.ilkd.key.java.declaration.modifier.Private;
import de.uka.ilkd.key.java.declaration.modifier.Protected;
import de.uka.ilkd.key.java.declaration.modifier.Static;
import de.uka.ilkd.key.java.recoderext.InstanceAllocationMethodBuilder;
import de.uka.ilkd.key.java.reference.MethodReference;
import de.uka.ilkd.key.java.reference.TypeRef;
import de.uka.ilkd.key.java.reference.TypeReference;
import de.uka.ilkd.key.java.statement.Return;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.logic.op.ProgramVariable;

/**
 * This class creates the <code>&lt;createArray&gt;</code> method for
 * array creation and in particular its helper method 
 * <code>&lt;createArrayHelper&gt;</code>. This class should be replaced
 * by a recoder transformation as soon as we port our array data
 * structures to RecodeR.
 */
public class CreateTransientArrayMethodBuilder extends CreateArrayMethodBuilder {
    
    /** current type for byte */
    private final KeYJavaType byteType;

    /** create the method builder for transient array implicit creation methods */
    public CreateTransientArrayMethodBuilder(KeYJavaType integerType, 
					     KeYJavaType objectType,
					     KeYJavaType byteType) {
	super(integerType, objectType);
	this.byteType = byteType;
    }

    /**
     * create the method declaration of the
     * <code>&lt;createArrayHelper&gt;</code> method for transient arrays
     */
    public ProgramMethod getCreateTransientArrayHelperMethod
	(TypeReference arrayTypeReference,
	 ProgramVariable length, 
	 ImmutableList<Field> fields) {
	
	final Modifier[] modifiers = new Modifier[] { new Private() };
	final KeYJavaType arrayType = arrayTypeReference.getKeYJavaType();

	final ProgramVariable pvLength = new LocationVariable
	    (new ProgramElementName("length"), integerType);

	final ProgramVariable pvTransientType = new LocationVariable
	    (new ProgramElementName("event"), integerType);

	final ParameterDeclaration param = 
	    new ParameterDeclaration(new Modifier[0], 
				     new TypeRef(integerType), 
				     new VariableSpecification(pvLength), 
				     false);

	final ParameterDeclaration paramTransientType = 
	    new ParameterDeclaration(new Modifier[0], 
				     new TypeRef(integerType), 
				     new VariableSpecification(pvTransientType), 
				     false);

	final MethodDeclaration md = new MethodDeclaration
	    (modifiers, 
	     arrayTypeReference, 
	     new ProgramElementName(IMPLICIT_ARRAY_TRANSIENT_CREATION_HELPER),
	     new ParameterDeclaration[]{param, paramTransientType}, null,
	     getCreateArrayHelperBody(length, 
				      pvLength, 
				      fields, 
				      true, pvTransientType), 
	     false);

	return new ProgramMethod(md, arrayType, arrayType, 
				 PositionInfo.UNDEFINED);
    }


    private StatementBlock getCreateTransientArrayBody
	(TypeReference arrayRef,
	 ProgramVariable paramLength,
	 ProgramVariable paramTransientType) {

 	final LocalVariableDeclaration local = 
            declare(new ProgramElementName("newObject"), arrayRef);	
	final ProgramVariable newObject      = (ProgramVariable) local.
	    getVariables().get(0).getProgramVariable();
	final LinkedList<Statement> body     = new LinkedList<Statement>();

	body.addLast(local);
	
        body.addLast
        (assign(newObject,
                new MethodReference
                 (new ImmutableArray<Expression>(new Expression[]{}), 
                      new ProgramElementName
                     (InstanceAllocationMethodBuilder.IMPLICIT_INSTANCE_ALLOCATE), 
                      arrayRef)));
   
 	body.add(new MethodReference
		 (new ImmutableArray<Expression>(new Expression[]
		     {paramLength, paramTransientType}), new ProgramElementName
		  (IMPLICIT_ARRAY_TRANSIENT_CREATION_HELPER), 
		  newObject));	

	body.add(new Return(newObject));

	return new StatementBlock
	    (body.toArray(new Statement[body.size()]));
    }


    /**
     * create the implicit creation method
     * <code>createTransientArray</code> 
     */
    public ProgramMethod getCreateTransientArrayMethod(TypeReference arrayTypeReference, 
						       ProgramVariable length,
						       ProgramMethod prepare,
						       ImmutableList<Field> fields) {

	final Modifier[] modifiers = new Modifier[] { new Protected(),
						      new Static() };
	
	final KeYJavaType arrayType = arrayTypeReference.getKeYJavaType();


	final ProgramVariable pvLength = new LocationVariable
	    (new ProgramElementName("length"), integerType);
	
	final ProgramVariable pvTransientType = 	    
	    (new LocationVariable(new ProgramElementName("event"), byteType));
	
	final ParameterDeclaration paramLength = new ParameterDeclaration
	    (new Modifier[0], new TypeRef(integerType), 
	     new VariableSpecification(pvLength), false);

	final ParameterDeclaration transientType = new ParameterDeclaration
	    (new Modifier[0], new TypeRef(byteType), 
	     new VariableSpecification(pvTransientType), false);


	final MethodDeclaration md = new MethodDeclaration
	    (modifiers, 
	     arrayTypeReference, 
	     new ProgramElementName(IMPLICIT_ARRAY_CREATE_TRANSIENT),
	     new ParameterDeclaration[]{paramLength, transientType}, null,
	     getCreateTransientArrayBody(arrayTypeReference, pvLength, pvTransientType), 
	     false);

	return new ProgramMethod(md, arrayType, arrayType, PositionInfo.UNDEFINED);
    }
}

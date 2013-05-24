// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 


package de.uka.ilkd.key.java.recoderext;

import java.util.*;

import recoder.CrossReferenceServiceConfiguration;
import recoder.java.Expression;
import recoder.java.Identifier;
import recoder.java.Statement;
import recoder.java.StatementBlock;
import recoder.java.declaration.*;
import recoder.java.declaration.modifier.Public;
import recoder.java.declaration.modifier.Static;
import recoder.java.reference.*;
import recoder.java.statement.Return;
import recoder.kit.*;
import recoder.list.generic.ASTArrayList;
import recoder.list.generic.ASTList;

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
public class CreateObjectBuilder extends RecoderModelTransformer {

    public static final String IMPLICIT_OBJECT_CREATE = "<createObject>";
    public static final String NEW_OBJECT_VAR_NAME = "__NEW__";
    private HashMap<ClassDeclaration, Identifier> class2identifier;


    public CreateObjectBuilder
	(CrossReferenceServiceConfiguration services, 
	 TransformerCache cache) {	
	super(services, cache);
	class2identifier = new LinkedHashMap<ClassDeclaration, Identifier>();
    }

   
    /** 
     * Creates the body of the static <code>&lt;createObject&gt;</code>
     * method.
     */
    private StatementBlock createBody(ClassDeclaration recoderClass) {
		
	ASTList<Statement> result = new ASTArrayList<Statement>(10);
	LocalVariableDeclaration local = declare(NEW_OBJECT_VAR_NAME, class2identifier.get(recoderClass));
	

	result.add(local);

	final ASTList<Expression> arguments = new ASTArrayList<Expression>(0);
       
        result.add
            (assign(new VariableReference
                    (new Identifier(NEW_OBJECT_VAR_NAME)),
                    new MethodReference(new TypeReference
                         (class2identifier.get(recoderClass)), 
                         new ImplicitIdentifier
                         (InstanceAllocationMethodBuilder.IMPLICIT_INSTANCE_ALLOCATE),
                         arguments)));

	MethodReference createRef = 
	    (new MethodReference(new VariableReference
				 (new Identifier(NEW_OBJECT_VAR_NAME)), 
				 new ImplicitIdentifier
				 (CreateBuilder.IMPLICIT_CREATE)));
	
	// July 08 - mulbrich: wraps createRef into a method body statement to
	// avoid unnecessary dynamic dispatch.
	// Method body statement are not possible for anonymous classes, however.
	// Use a method call there
	if(recoderClass.getIdentifier() == null) {
	    // anonymous
	    result.add
        (new MethodReference(new VariableReference
                             (new Identifier(NEW_OBJECT_VAR_NAME)),
                             new ImplicitIdentifier
                             (CreateBuilder.IMPLICIT_CREATE)));
	} else {
	    TypeReference tyref;
	    tyref = makeTyRef(recoderClass); 
	    result.add(new MethodBodyStatement(tyref, null, createRef));
	}
	
	// TODO why does the method return a value? Is the result ever used??
	result.add(new Return
		 (new VariableReference(new Identifier(NEW_OBJECT_VAR_NAME))));

	return new StatementBlock(result);
	
    }

    /* 
     * make a type reference. There are special classes which need to be handled 
     * differently. (<Default> for instance) 
     */
    private TypeReference makeTyRef(ClassDeclaration recoderClass) {
        Identifier id = recoderClass.getIdentifier();
        if(id instanceof ImplicitIdentifier) 
            return new TypeReference(id);
        else 
            return TypeKit.createTypeReference(getProgramFactory(), recoderClass);
    }
    

    /**
     * creates the implicit static <code>&lt;createObject&gt;</code>
     * method that takes the object to be created out of the pool
     * @param type the TypeDeclaration for which the
     * <code>&lt;prepare&gt;</code> is created
     * @return the implicit <code>&lt;prepare&gt;</code> method
     */
    public MethodDeclaration createMethod(ClassDeclaration type) {
	ASTList<DeclarationSpecifier> modifiers = new ASTArrayList<DeclarationSpecifier>(2);
	modifiers.add(new Public());
	modifiers.add(new Static());	

	MethodDeclaration md =  new MethodDeclaration
	    (modifiers, 
	     new TypeReference(class2identifier.get(type)), 
	     new ImplicitIdentifier(IMPLICIT_OBJECT_CREATE), 
	     new ASTArrayList<ParameterDeclaration>(0), 
	     null,
	     createBody(type));
	md.makeAllParentRolesValid();
	return md;
    }    

    public ProblemReport analyze() {
        for (final ClassDeclaration cd : classDeclarations()) {
            class2identifier.put(cd, getId(cd));
        }
        setProblemReport(NO_PROBLEM);
        return NO_PROBLEM;
    }

    /**
     * entry method for the constructor normalform builder
     * @param td the TypeDeclaration 
     */
    protected void makeExplicit(TypeDeclaration td) {
	if (td instanceof ClassDeclaration) {           
	    attach(createMethod((ClassDeclaration)td), td, 
	            td.getMembers().size());
//  	    java.io.StringWriter sw = new java.io.StringWriter();
//  	    services.getProgramFactory().getPrettyPrinter(sw).visitClassDeclaration((ClassDeclaration)td);
//  	    System.out.println(sw.toString());
//  	    try { sw.close(); } catch (Exception e) {}		
	}
    }






}

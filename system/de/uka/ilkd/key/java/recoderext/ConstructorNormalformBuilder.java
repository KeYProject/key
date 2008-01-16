// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
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

import java.util.*;

import recoder.CrossReferenceServiceConfiguration;
import recoder.abstraction.*;
import recoder.java.*;
import recoder.java.declaration.*;
import recoder.java.declaration.modifier.Private;
import recoder.java.declaration.modifier.Public;
import recoder.java.expression.operator.CopyAssignment;
import recoder.java.reference.*;
import recoder.kit.ProblemReport;
import recoder.list.*;
import de.uka.ilkd.key.util.Debug;

/**
 * Transforms the constructors of the given class to their
 * normalform. The constructor normalform can then be accessed via a
 * methodcall <code>&lt;init&gt;<cons_args)</code>. The visibility of
 * the normalform is the same as for the original constructor.
 */
public class ConstructorNormalformBuilder 
    extends RecoderModelTransformer {

    public static final String 
	CONSTRUCTOR_NORMALFORM_IDENTIFIER = "<init>";

    public static final String 
	OBJECT_INITIALIZER_IDENTIFIER = "<objectInitializer>";
        
    private HashMap class2constructors;
    private HashMap class2enclosingThis;
    private HashMap class2enclosingClass;
    private HashMap class2initializers;
    private HashMap class2identifier;
    private HashMap class2methodDeclaration;

    private ClassType javaLangObject;

    /** creates the constructor normalform builder */
    public ConstructorNormalformBuilder
	(CrossReferenceServiceConfiguration services, 
	 CompilationUnitMutableList units) {	
	super(services, units);
	class2constructors = new HashMap(4*units.size());
	class2initializers = new HashMap(10*units.size());
	class2methodDeclaration = new HashMap(10*units.size());
	class2enclosingThis = new HashMap(units.size());
	class2enclosingClass = new HashMap(units.size());
	class2identifier = new HashMap(units.size());
    }


    /**
     * The list of statements is the smallest list that contains a copy
     * assignment for each instance field initializer of class cd,
     * e.g. <code> i = 0; </code> for <code> public int i = 0; </code> or
     * a reference to the private method
     * <code>&lt;objectInitializer&gt;<i>i</i> refering to the i-th object
     * initializer of cd. These private declared methods are created on
     * the fly. Example for 
     *  <code> 
     *    class C { 
     *        int i = 0; 
     *        { 
     *            int j = 3; 
     *            i = j + 5;
     *        }
     *      
     *        public C () {} ...
     *   }
     *  </code> the following list of size two is returned
     *  <code> 
     *   [ i = 0;,  &lt;objectInitializer&gt;0(); ]
     *  </code>
     *  where <code>
     *    private &lt;objectInitializer&gt;0() {
     *       int j = 3; 
     *       i = j + 5;
     *    }
     *  </code>
     * @param cd the ClassDeclaration of which the initilizers have to
     * be collected
     * @return the list of copy assignments and method references
     * realising the initializers. 
     */
    private StatementList collectInitializers(ClassDeclaration cd) {
	StatementMutableList result = new StatementArrayList(20);
	MethodDeclarationMutableList mdl = new MethodDeclarationArrayList(5);
	int childCount = cd.getChildCount();
	for (int i = 0; i<childCount; i++) {
	    if (cd.getChildAt(i) instanceof ClassInitializer &&
		!((ClassInitializer)cd.getChildAt(i)).isStatic()) {

		ModifierMutableList mods = new ModifierArrayList(1);
		mods.add(new Private());
		String name = OBJECT_INITIALIZER_IDENTIFIER + mdl.size();
		MethodDeclaration initializerMethod = 
		    new MethodDeclaration
		    (mods,
		     null, //return type is void
		     new ImplicitIdentifier(name),
		     new ParameterDeclarationArrayList(0),
		     null,
		     (StatementBlock)
		     ((ClassInitializer)cd.getChildAt(i)).getBody().deepClone());		
		initializerMethod.makeAllParentRolesValid();
		mdl.add(initializerMethod);
		result.add(new MethodReference
			   (null,
			    new ImplicitIdentifier(name)));			   
	    } else if (cd.getChildAt(i) instanceof FieldDeclaration &&
		       !((FieldDeclaration)cd.getChildAt(i)).isStatic()) {
		FieldSpecificationList specs =
		    ((FieldDeclaration)cd.getChildAt(i)).getFieldSpecifications();
		for (int j = 0; j < specs.size(); j++) {
		    Expression fieldInit = null;
		    if ((fieldInit = specs.getFieldSpecification(j).			 
			 getInitializer()) != null) {
			CopyAssignment fieldCopy = 
			    new CopyAssignment
			    (new FieldReference
			     (new ThisReference(), 
			      specs.getFieldSpecification(j).getIdentifier()),
                              (Expression)fieldInit.deepClone());
			result.add(fieldCopy);
		    }
		}
	    }
	}
	class2methodDeclaration.put(cd, mdl);
	return result;
    }
    
    /**
     * Two-pass transformation have to be strictly divided up into two
     * parts. the first part analyzes the model and collects all
     * necessary information. In this case all class declarations are
     * examined and initializers as well as constructors are collected. 
     *   All actions, which may cause a recoder model update have to be
     * done here.
     * @return status report if analyze encountered problems or not
     */
    public ProblemReport analyze() {
        javaLangObject = services.getNameInfo().getJavaLangObject();
	 if (!(javaLangObject instanceof ClassDeclaration)) {
	     Debug.fail("Could not find class java.lang.Object or only as bytecode");
	 }
	 HashSet cds = classDeclarations();
	 Iterator it = cds.iterator();
	 while(it.hasNext()){
	     ClassDeclaration cd = (ClassDeclaration) it.next();
       
	     // collect constructors for transformation phase
             ConstructorMutableList constructors = new ConstructorArrayList(10);
             constructors.add(services.getSourceInfo().getConstructors(cd));
             if(constructors.size()==0){
                 System.out.println("no constructors: "+cd.getFullName());
                 constructors.add(new DefaultConstructor(cd));
             }
             class2constructors.put(cd, constructors);
             
             class2identifier.put(cd, getId(cd));
             
             class2enclosingThis.put(cd, getImplicitEnclosingThis(cd));
             if(cd.getName()==null || 
                     cd.getStatementContainer() !=null ||
                     cd.getContainingClassType()!=null){
                 class2enclosingClass.put(cd, containingClass(cd));
             }
             
             // collect initializers for transformation phase
             class2initializers.put(cd, collectInitializers(cd)); 
	 }
	 /*for (int unit = 0; unit<units.size(); unit++) {
	     CompilationUnit cu = units.getCompilationUnit(unit);
	     int typeCount = cu.getTypeDeclarationCount();
	
	     for (int i = 0; i < typeCount; i++) {
		if (cu.getTypeDeclarationAt(i) instanceof ClassDeclaration)
		    { 
			ClassDeclaration cd = (ClassDeclaration)
			    cu.getTypeDeclarationAt(i);
			if (cd.getTypeDeclarationCount()>0) {
			    Debug.out
				("consNFBuilder: Inner Class detected." + 
				 "No constructor normalform will be built" +
				 "for the inner classes of "+cd.getIdentifier());
			}
			
			// collect constructors for transformation phase
			ConstructorMutableList constructors = 
			    new ConstructorArrayList(10);
			constructors.add(services.getSourceInfo().getConstructors(cd));
			class2constructors.put(cd, constructors);
						
			// collect initializers for transformation phase
			class2initializers.put(cd, collectInitializers(cd));
		    }
	    }	
	}*/
	setProblemReport(NO_PROBLEM);
	return NO_PROBLEM;
    }
    
    protected Field getImplicitEnclosingThis(ClassDeclaration cd){
        FieldList fl = cd.getAllFields();
        for(int i=0; i<fl.size(); i++){
            if(fl.getField(i).getName().equals(ImplicitFieldAdder.IMPLICIT_ENCLOSING_THIS)){
                return fl.getField(i);
            }
        }
        return null;
    }

    private void attachDefaultConstructor(ClassDeclaration cd){
        ModifierMutableList mods = new ModifierArrayList(5);
        ParameterDeclarationMutableList parameters;
        Throws recThrows;
        StatementBlock body;
        mods.add(new Public());
        parameters = new ParameterDeclarationArrayList(0);
        recThrows = null;
        body = new StatementBlock();
        body.setBody(new StatementArrayList());
        attach(new MethodReference
                (new SuperReference(), new ImplicitIdentifier
                    (CONSTRUCTOR_NORMALFORM_IDENTIFIER)), body, 0);
        StatementMutableList initializers = (StatementMutableList) class2initializers.get(cd);
        for (int i = 0; i<initializers.size(); i++) {
            attach((Statement) 
                    initializers.getStatement(i).deepClone(),
                    body, i+1);
        }
        MethodDeclaration def =  new MethodDeclaration(mods,
                new TypeReference((Identifier) class2identifier.get(cd)),
                new ImplicitIdentifier(CONSTRUCTOR_NORMALFORM_IDENTIFIER),
                parameters,
                recThrows,
                body);
        def.makeAllParentRolesValid();
        attach(def, cd, 0);
    }
    
    /**
     * Creates the normalform of the given constructor, that is declared
     * in class cd. For a detailed description of the normalform to be
     * built see the KeY Manual.
     * @param cd the ClassDeclaration where the cons is declared
     * @param cons the Constructor to be transformed
     * @return the constructor normalform
     */
    private MethodDeclaration normalform(ClassDeclaration cd, 
					 Constructor cons) {	
	
	ModifierMutableList mods = new ModifierArrayList(5);
	ParameterDeclarationMutableList parameters;
	Throws recThrows;
	StatementBlock body;
	Field et = (Field) class2enclosingThis.get(cd);
	TypeDeclaration td = (TypeDeclaration) class2enclosingClass.get(cd);
	int j = et==null? 0 : 1;
	ParameterDeclaration pd=null;
        CopyAssignment ca = null;
        String etId = "_ENCLOSING_THIS";
	if(et!=null){
	    pd = new ParameterDeclaration(
	            new TypeReference((Identifier) td.getIdentifier().deepClone()), 
	            new Identifier(etId));
	    ca = new CopyAssignment(new FieldReference(new ThisReference(), new ImplicitIdentifier(et.getName())),
	                new VariableReference(new Identifier(etId)));
	}
	
	if (!(cons instanceof ConstructorDeclaration)) {
	    mods.add(new Public());
	    parameters = new ParameterDeclarationArrayList(0+j);
	    recThrows = null;
	    body = new StatementBlock();
	} else {
	    ConstructorDeclaration consDecl = (ConstructorDeclaration)cons;
	    mods = (ModifierMutableList)
		(consDecl.getModifiers()==null ? null : consDecl.getModifiers().deepClone());	    
	    parameters = 
		(ParameterDeclarationMutableList)consDecl.getParameters().deepClone();
	    recThrows = (Throws) (consDecl.getThrown() == null ? null : 
				  consDecl.getThrown().deepClone());
	    body = (StatementBlock) consDecl.getBody().deepClone();
	}
	if(pd!=null){    
	    if(parameters.isEmpty()){
	        attachDefaultConstructor(cd);
	    }
	    parameters.add(pd);
	}
	
	if (cd != javaLangObject) {
	    // remember original first statement
	    Statement first = body.getStatementCount() > 0 ?
		body.getStatementAt(0) : null;
	    
	    // first statement has to be a this or super constructor call	
	    if (!(first instanceof SpecialConstructorReference)) {
		if (body.getBody() == null) {
		    body.setBody(new StatementArrayList());
		}
		attach(new MethodReference
		    (new SuperReference(), new ImplicitIdentifier
			(CONSTRUCTOR_NORMALFORM_IDENTIFIER)), body, 0);
	    } else {
		body.getBody().remove(0);
		if(first instanceof ThisConstructorReference){
		    attach(new MethodReference
		            (new ThisReference(), new ImplicitIdentifier
		                    (CONSTRUCTOR_NORMALFORM_IDENTIFIER), 
		                    ((SpecialConstructorReference)first).getArguments()), body, 0);
		}else{
		    ReferencePrefix referencePrefix = ((SuperConstructorReference) first).getReferencePrefix();
		    ExpressionMutableList args = ((SpecialConstructorReference)first).getArguments();
		    if(referencePrefix!=null && referencePrefix instanceof Expression){
		        if(args==null) args = new ExpressionArrayList(1);
		        args.add((Expression) referencePrefix);
		    }
		    attach(new MethodReference
		            (new SuperReference(), new ImplicitIdentifier
		                    (CONSTRUCTOR_NORMALFORM_IDENTIFIER), 
		                    args),
		                    body, 0);	    
		}
	    }
	    // if the first statement is not a this constructor reference
	    // the instance initializers have to be added in source code
	    // order
	    if (!(first instanceof ThisConstructorReference)) {
		StatementMutableList initializers = (StatementMutableList)
		    class2initializers.get(cd);
		if(ca!=null){
		    attach(ca, body, 0);
		}
		for (int i = 0; i<initializers.size(); i++) {
		    attach((Statement) 
			   initializers.getStatement(i).deepClone(),
			   body, i+1+j);
		}
	    }
	}

	
	MethodDeclaration nf =  new MethodDeclaration
	    (mods,
	     new TypeReference((Identifier) class2identifier.get(cd)),
	     new ImplicitIdentifier(CONSTRUCTOR_NORMALFORM_IDENTIFIER),
	     parameters,
	     recThrows,
	     body);
	nf.makeAllParentRolesValid();
	System.out.println("nf.toSource: "+nf.toSource());
	return nf;
    }
      
    /**
     * entry method for the constructor normalform builder
     * @param td the TypeDeclaration 
     */
    protected void makeExplicit(TypeDeclaration td) {
	if (td instanceof ClassDeclaration) {
	    ConstructorMutableList constructors = 
		(ConstructorMutableList) class2constructors.get(td);
	    for (int i = 0; i < constructors.size(); i++) {
		attach(normalform
		       ((ClassDeclaration)td, 
			constructors.getConstructor(i)), td, 0);
	    }	    

	    MethodDeclarationList mdl = (MethodDeclarationList)class2methodDeclaration.get(td);
	    for (int i = 0; i < mdl.size(); i++) {
		attach(mdl.getMethodDeclaration(i), td, 0);
	    }

/*  	    java.io.StringWriter sw = new java.io.StringWriter();
//  	    //services.getProgramFactory().getPrettyPrinter(sw).visitMethodDeclaration(nf);
  	    services.getProgramFactory().getPrettyPrinter(sw).visitClassDeclaration((ClassDeclaration)td);
  	    System.out.println(sw.toString());
  	    try { sw.close(); } catch (Exception e) {}		*/
	}


    }
    
    


}

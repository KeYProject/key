// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
// 
package de.uka.ilkd.key.java.recoderext;

import java.util.*;

import recoder.CrossReferenceServiceConfiguration;
import recoder.abstraction.ClassType;
import recoder.java.CompilationUnit;
import recoder.abstraction.Variable;
import recoder.java.Identifier;
import recoder.java.declaration.*;
import recoder.java.declaration.modifier.*;
import recoder.java.declaration.DeclarationSpecifier;
import recoder.java.reference.TypeReference;
import recoder.kit.ProblemReport;
import recoder.list.generic.ASTArrayList;
import recoder.list.generic.ASTList;
import de.uka.ilkd.key.util.Debug;


/**
 * The Java DL requires some implicit fields and methods, that are
 * available in each Java class. The name of the implicit fields/methods
 * is usually enclosed between two angle brackets. To access them in a
 * uniform way, they are added as usual fields to the classes, in
 * particular this makes it possible to parse them in a natural way.
 *   The ImplicitFieldAdder is responsible to add all implicit fields to
 * the type declarations of the model. As the implicit methods and only
 * them will access these fields, this transformer has to be executed
 * before the other transformers are called.
 */
public class ImplicitFieldAdder extends RecoderModelTransformer {

    public static final String IMPLICT_ARRAY_TRA_INITIALIZED = "<traInitialized>";

    public static final String IMPLICIT_CLASS_PREPARED = "<classPrepared>";
    public static final String IMPLICIT_CLASS_INITIALIZED = "<classInitialized>";
    public static final String IMPLICIT_CLASS_INIT_IN_PROGRESS = "<classInitializationInProgress>";
    public static final String IMPLICIT_CLASS_ERRONEOUS = "<classErroneous>";

    public static final String IMPLICIT_NEXT_TO_CREATE = "<nextToCreate>";
    public static final String IMPLICIT_CREATED = "<created>";
    
    public static final String IMPLICIT_INITIALIZED = "<initialized>";
    public static final String IMPLICIT_TRANSIENT = "<transient>";
    
    public static final String IMPLICIT_ENCLOSING_THIS = "<enclosingThis>";
    
    public static final String FINAL_VAR_PREFIX = "_outer_final_";
 
    /** flag set if java.lang.Object has been already transformed */
    private boolean transformedObject = false;
    private ClassType javaLangObject;

    /**
     * creates a transformation that adds all implicit fields,
     * for example <code>&lt;created&gt;</code>,
     * <code>&lt;initialized&gt;</code> and
     * <code>&lt;nextToCreate&gt;</code> etc. 
     * @param services the CrossReferenceServiceConfiguration to access 
     * model information
     * @param units the array of CompilationUnits describing the model
     * to be transformed
     */
    public ImplicitFieldAdder
	(CrossReferenceServiceConfiguration services, 
	 List<CompilationUnit> units) {	
	super(services, units);
    }

    /**
     * creates an implicit field of the given type and name
     * @param typeName the name of the type of the new field to create
     * @param fieldName the name of the field
     * @param isStatic a boolean that is true if the field has to be
     * created as static (class) field
     * @return the new created field declaration
     */
    public static FieldDeclaration createImplicitRecoderField
	(String typeName, String fieldName, 
	 boolean isStatic, boolean isPrivate) {
	
	ASTList<DeclarationSpecifier> modifiers = new ASTArrayList<DeclarationSpecifier>
	    (1 + (isStatic ? 1 : 0));

	if (isStatic) {
	    modifiers.add(new Static());
	} 
	if (isPrivate) {
	    modifiers.add(new Private());
	} else {
	    modifiers.add(new Public());
	}
	
	Identifier id = typeName.charAt(0) == '<' ? 
	    new ImplicitIdentifier(typeName) : new Identifier(typeName);
	
	FieldDeclaration fd = new FieldDeclaration
	    (modifiers, new TypeReference(id), 
	     new ImplicitIdentifier(fieldName), null);
	
	fd.makeAllParentRolesValid();

	return fd;
    }


    /**
     * The implicit fields divide up into two categories. Global fields
     * declared just in java.lang.Object and type specific one declared
     * in each reference type. This method adds the global ones.
     */
    private void addGlobalImplicitRecoderFields(TypeDeclaration td) {
	// instance
        attach(createImplicitRecoderField("byte", IMPLICIT_TRANSIENT, false, false), td, 0);
	attach(createImplicitRecoderField("boolean", IMPLICIT_INITIALIZED, false, false), td, 0);
        attach(createImplicitRecoderField("boolean", IMPLICIT_CREATED, false, false), td, 0);
    }
    

    /** 
     * adds implicit fields to the given type declaration
     * @param td the recoder.java.TypeDeclaration to be enriched with
     * implicit fields 
     */
    private void addImplicitRecoderFields
    (recoder.java.declaration.TypeDeclaration td) {

	// static
/*	String className = td.getName(); 
	if (className == null) {
	    Debug.out("makeImplicitMembersExplicit: anonymous class will not add" +
		      "implicit fields");
	    return;
	}*/
	attach(createImplicitRecoderField("boolean", IMPLICIT_CLASS_INIT_IN_PROGRESS, true, true), td, 0);
	attach(createImplicitRecoderField("boolean", IMPLICIT_CLASS_ERRONEOUS, true, true), td, 0);
	attach(createImplicitRecoderField("boolean", IMPLICIT_CLASS_INITIALIZED, true, true), td, 0);
	attach(createImplicitRecoderField("boolean", IMPLICIT_CLASS_PREPARED, true, true), td, 0);
	
	if(td instanceof ClassDeclaration && 
	        (td.getName()==null || 
	                ((ClassDeclaration) td).getStatementContainer() !=null ||
	                ((ClassDeclaration) td).getContainingClassType()!=null) &&
	                (containingMethod(td)==null || !containingMethod(td).isStatic()) &&
	                !td.isStatic()){
	    ClassDeclaration container = containingClass(td);
	    ModifierMutableList modifiers = new ModifierArrayList(1);
	    modifiers.add(new Private());
	    Identifier id = getId(container);
        
            FieldDeclaration fd = new FieldDeclaration
                (modifiers, new TypeReference(id), 
                        new ImplicitIdentifier(IMPLICIT_ENCLOSING_THIS), null);
            fd.makeAllParentRolesValid();
	    attach(fd, td, 0);
	}
	  
        
	if (!td.isInterface() && !td.isAbstract()) {	  
	    attach(createImplicitRecoderField("int", 
					      IMPLICIT_NEXT_TO_CREATE, true, true), td, 0);
	}
    }
    
    private void addFieldsForFinalVars(TypeDeclaration td){
        LinkedList vars = (LinkedList) localClass2FinalVar.get(td);
        if(vars!=null){
            Iterator it = vars.iterator();
            while(it.hasNext()){
                Variable v = (Variable) it.next();
                attach(createImplicitRecoderField(v.getType().getName(), FINAL_VAR_PREFIX+v.getName(), false, true), td, 0);
            }
        }
    }

    
    public ProblemReport analyze() {
        javaLangObject = services.getNameInfo().getJavaLangObject();
	 if (!(javaLangObject instanceof ClassDeclaration)) {
	     Debug.fail("Could not find class java.lang.Object or only as bytecode");
	 }
	 HashSet cds = classDeclarations();
	 Iterator it = cds.iterator();
	 while(it.hasNext()){
	     ClassDeclaration cd = (ClassDeclaration) it.next();
	     if(cd.getName()==null || cd.getStatementContainer() !=null){
	         (new FinalOuterVarsCollector()).walk(cd);
	     }
	 }     
	 return super.analyze();
    }
    
    
    protected void makeExplicit(TypeDeclaration td) {

	addImplicitRecoderFields(td);
	
	addFieldsForFinalVars(td);

	if (!transformedObject && td == javaLangObject) {	   
	    addGlobalImplicitRecoderFields(td);
	    transformedObject = true;			    
	}
	td.makeAllParentRolesValid();
// 	if (td instanceof ClassDeclaration) {
// 	    java.io.StringWriter sw = new java.io.StringWriter();
// 	    services.getProgramFactory().getPrettyPrinter(sw).visitClassDeclaration((ClassDeclaration)td);
// 	    System.out.println(sw.toString());
// 	    try { sw.close(); } catch (Exception e) {}	   
// 	}
    }
}

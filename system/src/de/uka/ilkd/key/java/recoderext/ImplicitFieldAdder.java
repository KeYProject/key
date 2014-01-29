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

import java.util.List;

import recoder.CrossReferenceServiceConfiguration;
import recoder.abstraction.ClassType;
import recoder.abstraction.Variable;
import recoder.java.Identifier;
import recoder.java.declaration.*;
import recoder.java.declaration.modifier.*;
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

    public static final String IMPLICIT_CLASS_PREPARED = "<classPrepared>";
    public static final String IMPLICIT_CLASS_INITIALIZED = "<classInitialized>";
    public static final String IMPLICIT_CLASS_INIT_IN_PROGRESS = "<classInitializationInProgress>";
    public static final String IMPLICIT_CLASS_ERRONEOUS = "<classErroneous>";
    
    public static final String IMPLICIT_CREATED = "<created>";
   
    public static final String IMPLICIT_INITIALIZED = "<initialized>";

    public static final String IMPLICIT_TRANSIENT = "<transient>";
    public static final String IMPLICIT_TRANSACTION_UPDATED = "<transactionConditionallyUpdated>";
    
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
     * @param  cache a cache object that stores information which is needed by
     * and common to many transformations. it includes the compilation units,
     * the declared classes, and information for local classes.
     */
    public ImplicitFieldAdder(CrossReferenceServiceConfiguration services,
            TransformerCache cache) {
        super(services, cache);
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
        return createImplicitRecoderField(typeName, fieldName, isStatic, isPrivate, false);
    }
    
    public static FieldDeclaration createImplicitRecoderField
	(String typeName, String fieldName, 
	 boolean isStatic, boolean isPrivate, boolean isFinal) {
	
	final int modCount = 1 + (isStatic ? 1 : 0) + (isFinal ? 1 : 0); 
	ASTList<DeclarationSpecifier> modifiers = new ASTArrayList<DeclarationSpecifier>(modCount);

	if (isStatic) {
	    modifiers.add(new Static());
	} 
	if (isPrivate) {
	    modifiers.add(new Private());
	} else {
	    modifiers.add(new Public());
	}
        
        if(isFinal){
            modifiers.add(new Final());
        }
	
        int idx = typeName.indexOf('[');        
        final String baseType = (idx == -1 ? typeName : typeName.substring(0, idx));
        
	final Identifier id = typeName.charAt(0) == '<' ? 
	    new ImplicitIdentifier(baseType) : new Identifier(baseType);
	
	FieldDeclaration fd = new FieldDeclaration
	    (modifiers, new TypeReference(id, idx == -1 ? 0 : (typeName.length()-baseType.length())/2), 
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
	attach(createImplicitRecoderField("boolean", IMPLICIT_INITIALIZED, false, false), td, 0);
        attach(createImplicitRecoderField("boolean", IMPLICIT_CREATED, false, false), td, 0);	  
        attach(createImplicitRecoderField("int", IMPLICIT_TRANSIENT, false, false), td, 0);	  
        attach(createImplicitRecoderField("boolean", IMPLICIT_TRANSACTION_UPDATED, false, false), td, 0);	  
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
	                td.getContainingClassType()!=null) &&
	                (containingMethod(td)==null || !containingMethod(td).isStatic()) &&
	                !td.isStatic()){
	    ClassDeclaration container = containingClass(td);
	    ASTList<DeclarationSpecifier> modifiers = new ASTArrayList<DeclarationSpecifier>(1);
	    modifiers.add(new Private());
	    Identifier id = getId(container);
        
            FieldDeclaration fd = new FieldDeclaration
                (modifiers, new TypeReference(id), 
                        new ImplicitIdentifier(IMPLICIT_ENCLOSING_THIS), null);
            fd.makeAllParentRolesValid();
	    attach(fd, td, 0);
	}
    }
    
    protected void addClassInitializerStatusFields(
            recoder.java.declaration.TypeDeclaration td) {	
	attach(createImplicitRecoderField("boolean", IMPLICIT_CLASS_INIT_IN_PROGRESS, true, true), td, 0);
	attach(createImplicitRecoderField("boolean", IMPLICIT_CLASS_ERRONEOUS, true, true), td, 0);
	attach(createImplicitRecoderField("boolean", IMPLICIT_CLASS_INITIALIZED, true, true), td, 0);
	attach(createImplicitRecoderField("boolean", IMPLICIT_CLASS_PREPARED, true, true), td, 0);	
    }
    
    private void addFieldsForFinalVars(TypeDeclaration td){
        final List<Variable> vars = getLocalClass2FinalVar().get(td);
        if(vars != null){
            
            // not sure why, but doing it separated in two loops is much faster (for large programs) then just in one
            // strangely, the effect is not measureable for e.g. the class init. fields...
            FieldDeclaration[] newFields = new FieldDeclaration[vars.size()]; 
            
            int i = 0;
            for (final Variable var : vars) {
        	newFields[i] = createImplicitRecoderField(var.getType().getName(), FINAL_VAR_PREFIX + var.getName(), false, true); 
        	i++;
            }
            
            for (final FieldDeclaration fd : newFields) {
        	attach(fd, td, 0);
            }
        }
    }
    
    public ProblemReport analyze() {
        javaLangObject = services.getNameInfo().getJavaLangObject();
	 if (!(javaLangObject instanceof ClassDeclaration)) {
	     Debug.fail("Could not find class java.lang.Object or only as bytecode");
	 }
	 for (final TypeDeclaration cd : classDeclarations()) {
	     if(cd instanceof ClassDeclaration && 
                     (cd.getName()==null || ((ClassDeclaration) cd).getStatementContainer()!=null)){
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
// 	    Debug.printStackTrace();
// 	    try { sw.close(); } catch (Exception e) {}	   
// 	}
    }
    
}

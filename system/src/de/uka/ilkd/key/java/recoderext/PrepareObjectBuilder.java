// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.java.recoderext;

import java.util.*;

import recoder.CrossReferenceServiceConfiguration;
import recoder.abstraction.ClassType;
import recoder.abstraction.Field;
import recoder.java.*;
import recoder.java.declaration.*;
import recoder.java.declaration.modifier.Private;
import recoder.java.declaration.modifier.Protected;
import recoder.java.reference.*;
import recoder.kit.ProblemReport;
import recoder.list.generic.ASTArrayList;
import recoder.list.generic.ASTList;
import de.uka.ilkd.key.util.Debug;

/**
 * Creates the preparation method for pre-initilizing the object fields
 * with their default settings.
 */
public class PrepareObjectBuilder 
    extends RecoderModelTransformer {

    public static final String 
	IMPLICIT_OBJECT_PREPARE = "<prepare>";

    public static final String 
	IMPLICIT_OBJECT_PREPARE_ENTER = "<prepareEnter>";

    private HashMap<TypeDeclaration, ASTList<Statement>> class2fields;

    private ClassType javaLangObject;
    

    public PrepareObjectBuilder
	(CrossReferenceServiceConfiguration services, 
	 TransformerCache cache) {	
	super(services, cache);
	class2fields = new LinkedHashMap<TypeDeclaration, ASTList<Statement>>(getUnits().size());
    }

    /**
     * returns all fields of the class cd in source code order. The
     * method is a work around for a bug in recoder 0.70 as there source
     * code order is not respected. May become obsolete if newer recoder
     * versions are used.
     */
    private List<Field> getFields(ClassDeclaration cd) {
	List<Field> result = new ArrayList<Field>(cd.getChildCount());
	outer: for (int i = 0; i<cd.getChildCount(); i++) {
	    if (cd.getChildAt(i) instanceof FieldDeclaration) {
		final FieldDeclaration fd = (FieldDeclaration) cd.getChildAt(i);
		for(Modifier mod : fd.getModifiers()) {
		    if(mod instanceof Model) {
			continue outer;
		    }
		}
		final ASTList<FieldSpecification> fields 
			= fd.getFieldSpecifications();
		for (int j = 0; j<fields.size(); j++) {
		    result.add(fields.get(j));
		}
	    }
	}
	return result;	
    }

    /**
     * Two-pass transformation have to be strictly divided up into two
     * parts. the first part analyzes the model and collects all
     * necessary information. In this case all class declarations are
     * examined and for each found field a copy assignment to its
     * default value is added to the map "class2fields".
     *   All actions, which may cause a recoder model update have to be
     * done here.
     * @return status report if analyze encountered problems or not
     */
    public ProblemReport analyze() {
	javaLangObject = services.getNameInfo().getJavaLangObject();
        if (!(javaLangObject instanceof ClassDeclaration)) {
            Debug.fail("Could not find class java.lang.Object or only as bytecode");
        }
        for (final ClassDeclaration cd : classDeclarations()) {
            class2fields.put(cd, defaultSettings(getFields(cd)));
        }
	/*for (int unit = 0; unit<units.size(); unit++) {
        CompilationUnit cu = units.get(unit);
	    int typeCount = cu.getTypeDeclarationCount();
	
	    for (int i = 0; i < typeCount; i++) {
		if (cu.getTypeDeclarationAt(i) instanceof ClassDeclaration)
		    { 
			ClassDeclaration cd = (ClassDeclaration)
			    cu.getTypeDeclarationAt(i);
			if (cd.getTypeDeclarationCount()>0) {
			    Debug.out
				("prepare object builder: Inner Class detected." + 
				 "No class preparation method will be built" +
				 "for inner classes of "+cd.getIdentifier());
			}
			
			// collect fields for transformation phase

 			class2fields.put(cd, defaultSettings(getFields(cd)));
			//would be nice but in Recoder0.70 the source order is not respected
// 			class2fields.put(cd, defaultSettings(cd.getFields()));
		    }
	    }
	}*/
	setProblemReport(NO_PROBLEM);
	return NO_PROBLEM;
    }

    /**
     *  creates the assignments of the field variables to their default values
     * and inserts them to the given body list
     * @return the same list body that has been handed over as parameter
     */
    private ASTList<Statement> defaultSettings(List<Field> fields) {

	if (fields == null) {
	    return new ASTArrayList<Statement>(0);
	} 
	ASTList<Statement> result = new ASTArrayList<Statement>(fields.size());
        for (Field field : fields) {
	    if (!field.isStatic() ) {		
                Identifier fieldId;
                if (field.getName().charAt(0) != '<') {
                    fieldId = new Identifier(field.getName());
                    result.add
                            (assign((attribute(new ThisReference(), fieldId)),
                                    getDefaultValue
                                            (services.
                                                    getCrossReferenceSourceInfo().getType(field))));
                }
            }
        }
	
	return result;
    }

    /** 
     * creates an implicit method called 'prepare', that sets all
     * attributes to their default values
     */
    protected StatementBlock createPrepareBody
	(ReferencePrefix prefix, TypeDeclaration classType) {

	ASTList<Statement> body = new ASTArrayList<Statement>(15);

	if (classType != javaLangObject) {
	    // we can access the implementation	    	    
	    body.add((new MethodReference
			 (new SuperReference(), 
			  new ImplicitIdentifier(IMPLICIT_OBJECT_PREPARE))));
	    body.addAll(class2fields.get(classType));
        }
	return new StatementBlock(body);
    }
    
    /**
     * creates the implicit <code>&lt;prepare&gt;</code> method that
     * sets the fields of the given type to its default values
     * @param type the TypeDeclaration for which the
     * <code>&lt;prepare&gt;</code> is created
     * @return the implicit <code>&lt;prepare&gt;</code> method
     */
    public MethodDeclaration createMethod(TypeDeclaration type) {
	ASTList<DeclarationSpecifier> modifiers = new ASTArrayList<DeclarationSpecifier>(1);
	modifiers.add(new Protected());	
	//	modifiers.add(new KeYAnnotationUseSpecification(new TypeReference(
	//                new Identifier("ExternallyConstructedScope"))));
	//        modifiers.add(new KeYAnnotationUseSpecification(new TypeReference(
	//                new Identifier("NoLocalScope"))));
	MethodDeclaration md =  new MethodDeclaration
	    (modifiers, 
	     null, 
	     new ImplicitIdentifier(IMPLICIT_OBJECT_PREPARE), 
	     new ASTArrayList<ParameterDeclaration>(0), 
	     null,
	     createPrepareBody(new ThisReference(), type));
	md.makeAllParentRolesValid();
	return md;
    }    

    /**
     * creates the implicit <code>&lt;prepareEnter&gt;</code> method that
     * sets the fields of the given type to its default values
     * @param type the TypeDeclaration for which the
     * <code>&lt;prepare&gt;</code> is created
     * @return the implicit <code>&lt;prepare&gt;</code> method
     */
    public MethodDeclaration createMethodPrepareEnter(TypeDeclaration type) {
	ASTList<DeclarationSpecifier> modifiers = new ASTArrayList<DeclarationSpecifier>(1);
	modifiers.add(new Private());	
        
	//        modifiers.add(new KeYAnnotationUseSpecification(new TypeReference(
  	//              new Identifier("ExternallyConstructedScope"))));
 	//       modifiers.add(new KeYAnnotationUseSpecification(new TypeReference(
 	//               new Identifier("NoLocalScope"))));
        
	MethodDeclaration md =  new MethodDeclaration
	    (modifiers, 
	     null, 
	     new ImplicitIdentifier(IMPLICIT_OBJECT_PREPARE_ENTER), 
	     new ASTArrayList<ParameterDeclaration>(0), 
	     null,
	     createPrepareBody(new ThisReference(), type));
	md.makeAllParentRolesValid();
	return md;
    }    



    /**
     * entry method for the constructor normalform builder
     * @param td the TypeDeclaration 
     */
    protected void makeExplicit(TypeDeclaration td) {
	if (td instanceof ClassDeclaration) {
	    attach(createMethod(td), td, td.getMembers().size());
	    attach(createMethodPrepareEnter(td), td, td.getMembers().size());
// 	    java.io.StringWriter sw = new java.io.StringWriter();
// 	    services.getProgramFactory().getPrettyPrinter(sw).visitClassDeclaration((ClassDeclaration)td);
// 	    System.out.println(sw.toString());
// 	    try { sw.close(); } catch (Exception e) {}		
	}
    }

}
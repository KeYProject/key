// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
/**
 * 
 */
package de.uka.ilkd.key.java.recoderext;

import java.util.HashMap;

import de.uka.ilkd.key.java.abstraction.PrimitiveType;

import recoder.CrossReferenceServiceConfiguration;
import recoder.java.Identifier;
import recoder.java.declaration.ClassDeclaration;
import recoder.java.declaration.DeclarationSpecifier;
import recoder.java.declaration.MethodDeclaration;
import recoder.java.declaration.ParameterDeclaration;
import recoder.java.declaration.TypeDeclaration;
import recoder.java.declaration.modifier.Public;
import recoder.java.declaration.modifier.Static;
import recoder.java.reference.TypeReference;
import recoder.list.generic.ASTArrayList;
import recoder.list.generic.ASTList;

/**
 * @author gladisch
 * Transformations required for Verification-based Test generation. See package unittest.
 * Transformations are kept small to not distract KeY's "normal" verification behavior.
 * Current transformations:
 * - add a dummy method that nothing is known about. This method abstracts a loop after a bounded number of loop unwindings.
 * This class is integrated into KeY via Recorder2KeY.transformModel()
 * This functionality of this method is required by class key.rule.metaconstruct.WhileLoopTransformation2    
 */
public class TestGenerationModelTransformer extends RecoderModelTransformer {

    public static final String IMPLICIT_ABSTRACTION_METHOD = "<loopAbstraction>";

    public TestGenerationModelTransformer
	(CrossReferenceServiceConfiguration services, 
	 TransformerCache cache) {	
	super(services, cache);
}
    
    /**
     * Extends the classDeclaration given as parameter with the declaration of
     * the implicit method <code>&lt;loopAbstractionMethod&gt;</code>. The purpose of this
     * implicit method is to abstract program code. In order to distinguish
     * abstraction of different source codes the implicit method takes
     * as argument the hash value of the program code that it abstracts.
     * This ensures that abstractions of different codes do not unify as otherwise
     * the abstraction would be unsound.
     * 
     * @param type the TypeDeclaration for which the
     * <code>&lt;loopAbstractionMethod&gt;</code> is created
     * @return the implicit <code>&lt;loopAbstractionMethod&gt;</code> method
     * @see key.rule.metaconstruct.WhileLoopTransformation2
     */
    public MethodDeclaration createMethod(ClassDeclaration type) {
	ASTList<DeclarationSpecifier> modifiers = new ASTArrayList<DeclarationSpecifier>(2);
	modifiers.add(new Public());
	modifiers.add(new Static());	
	
	ASTArrayList<ParameterDeclaration> params= new ASTArrayList<ParameterDeclaration>();
	ParameterDeclaration param =   new ParameterDeclaration(
	            new TypeReference(new Identifier("long")), 
	            new Identifier("hashValueOfLoop"));
	params.add(param);

	MethodDeclaration md =  new MethodDeclaration
	    (modifiers, 
	     null, /*new TypeReference(class2identifier.get(type))*/ 
	     new ImplicitIdentifier(IMPLICIT_ABSTRACTION_METHOD), 
	     params, // new ASTArrayList<ParameterDeclaration>(0), 
	     null,
	     null/*createBody(type)*/);
	md.makeAllParentRolesValid();
	return md;
    }    

    /* adds an implicit method to java.lang.Object
     */
    protected void makeExplicit(TypeDeclaration td) {
	if (td instanceof ClassDeclaration && td.getFullName().equals("java.lang.Object")) {
	    attach(createMethod((ClassDeclaration)td), td, 
	            td.getMembers().size());
	}
    }

}

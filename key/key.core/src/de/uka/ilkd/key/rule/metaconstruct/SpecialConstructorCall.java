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

package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.java.KeYJavaASTFactory;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.reference.*;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * The constructor call meta construct is used to handle a allocation expression
 * like <code>new Class(...)</code>. Thereby it replaces the allocation 
 * expression by a method reference to an implict method called
 * <code>&lt;init&gt;</code> that is mainly the constructor but in its
 * normalform.
 */
public class SpecialConstructorCall extends ProgramTransformer {

    private static final ProgramElementName NORMALFORM_IDENTIFIER = 
        new ProgramElementName
        (de.uka.ilkd.key.java.recoderext.
         ConstructorNormalformBuilder.CONSTRUCTOR_NORMALFORM_IDENTIFIER);
    
    /** 
     * creates the metaconstruct
     */
    public SpecialConstructorCall(ProgramElement consRef) {
	super(new Name("special-constructor-call"), consRef);
    }

    /** 
     * transforms the constructor's body into its normalform and
     * returns the result. Thereby all necessary references are
     * resolved.     
     */
    public ProgramElement transform
	(ProgramElement pe, Services services, SVInstantiations svInst) {

	SpecialConstructorReference constructorReference = 
	    (SpecialConstructorReference) pe;

	ReferencePrefix prefix;
	if (constructorReference instanceof ThisConstructorReference) {
	    prefix = KeYJavaASTFactory.thisReference();
	} else {
	    prefix = KeYJavaASTFactory.superReference();
	}

	return KeYJavaASTFactory.methodCall(prefix, NORMALFORM_IDENTIFIER,
		constructorReference.getArguments());
    }

}
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


package de.uka.ilkd.key.speclang.jml.translation;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.FieldDeclaration;
import de.uka.ilkd.key.java.declaration.MemberDeclaration;
import de.uka.ilkd.key.java.declaration.modifier.Protected;
import de.uka.ilkd.key.java.declaration.modifier.Public;
import de.uka.ilkd.key.java.declaration.modifier.VisibilityModifier;
import de.uka.ilkd.key.logic.op.ParsableVariable;
import de.uka.ilkd.key.speclang.jml.JMLInfoExtractor;
import de.uka.ilkd.key.speclang.translation.*;


/**
 * Resolver manager for JML.
 */
final class JMLResolverManager extends SLResolverManager {

    public JMLResolverManager(JavaInfo javaInfo,
                              KeYJavaType specInClass,
                              ParsableVariable selfVar,
                              SLTranslationExceptionManager eManager) {
        super(eManager, specInClass, selfVar, false);
        addResolver(new JMLBuiltInPropertyResolver(javaInfo, this, specInClass));
        addResolver(new SLAttributeResolver(javaInfo, this, specInClass));        
        addResolver(new SLMethodResolver(javaInfo, this, specInClass));
        addResolver(new SLTypeResolver(javaInfo, this, specInClass));
    }
    
    
    @Override
    public VisibilityModifier getSpecVisibility(MemberDeclaration md) {
	if(JMLInfoExtractor.hasJMLModifier((FieldDeclaration)md, 
		                           "spec_public")) {
	    return new Public();
	} else if(JMLInfoExtractor.hasJMLModifier((FieldDeclaration)md, 
		                                  "spec_protected")) {
	    return new Protected();
	} else {
	    return null;
	}
    }    
}

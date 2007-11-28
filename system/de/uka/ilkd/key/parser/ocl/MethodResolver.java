// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//This file is part of KeY - Integrated Deductive Software Design
//Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                      Universitaet Koblenz-Landau, Germany
//                      Chalmers University of Technology, Sweden
//
//The KeY system is protected by the GNU General Public License. 
//See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.parser.ocl;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.util.AssertionFailure;


/**
 * Resolves method (query) calls.
 */
class MethodResolver implements PropertyResolver {
    
    private final Services services;
    private final JavaInfo javaInfo;
    private final FormulaBoolConverter fbc;
    
    
    public MethodResolver(Services services, FormulaBoolConverter fbc) {
        this.services = services;
        this.javaInfo = services.getJavaInfo();
        this.fbc      = fbc;
    }
    
    
    private boolean isFullyQualified(String name) {
        return name.indexOf("::") >= 0;
    }
    
    
    private String extractTypeName(String fullyQualifiedName) {
        return fullyQualifiedName.substring(0, 
                                            fullyQualifiedName.indexOf("::"));
    }
    
    
    private String extractPropertyName(String fullyQualifiedName) {
        return fullyQualifiedName.substring(fullyQualifiedName.indexOf("::")+2);
    }
    
    
    public OCLEntity resolve(OCLEntity receiver,
                             String name, 
                             OCLParameters parameters) throws OCLTranslationError {
        if(parameters == null || !parameters.getDeclaredVars().isEmpty()) {
            return null;
        }

        String containingName;
        if(isFullyQualified(name)) {
            containingName = extractTypeName(name);
            name = extractPropertyName(name);
        } else {
            KeYJavaType containingType 
                    = javaInfo.getKeYJavaType(receiver.getSort());
            if(containingType == null) {
        	return null;
            }
            containingName = containingType.getFullName();
        }
        
        Term[] args 
            = fbc.convertFormulasToBool(parameters.getEntities()).toArray();
           
        Term recTerm                = receiver.getTerm();
        KeYJavaType recType         = receiver.getType();
        OCLCollection recCollection = receiver.getCollection();       
        try {
            if(recTerm != null || recType != null) {
                
                Term methodTerm = javaInfo.getProgramMethodTerm(
                                receiver.getTerm(),
                                name,
                                args,
                                containingName);
                
                return new OCLEntity(methodTerm);
            } else if(recCollection != null) {
                Term recVarTerm = recCollection.getPredVarAsTerm();
                Term methodTerm = javaInfo.getProgramMethodTerm(
                                recVarTerm,
                                name,
                                args,
                                containingName);
                OCLCollection newCollection 
                        = recCollection.collect(services, methodTerm);
                return new OCLEntity(newCollection);
            }
        } catch(Exception e) {
        	if (e instanceof OCLTranslationError) {
        		throw (OCLTranslationError) e;
        	}
        }
                
        return null;
    }


    public boolean needVarDeclaration(String propertyName) {
        return false;
    }    
}

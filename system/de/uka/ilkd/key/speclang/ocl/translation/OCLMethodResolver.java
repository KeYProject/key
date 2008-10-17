//This file is part of KeY - Integrated Deductive Software Design
//Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                      Universitaet Koblenz-Landau, Germany
//                      Chalmers University of Technology, Sweden
//
//The KeY system is protected by the GNU General Public License. 
//See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.speclang.ocl.translation;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.speclang.translation.SLResolverManager;
import de.uka.ilkd.key.speclang.translation.SLExpression;
import de.uka.ilkd.key.speclang.translation.SLExpressionResolver;
import de.uka.ilkd.key.speclang.translation.SLParameters;
import de.uka.ilkd.key.speclang.translation.SLTranslationException;


/**
 * Resolves method (query) calls.
 */
class OCLMethodResolver extends SLExpressionResolver {
    
    private final Services services;
    private final FormulaBoolConverter fbc;
    
    public OCLMethodResolver(Services services, FormulaBoolConverter fbc, SLResolverManager man) {
        super(services.getJavaInfo(),man);
        this.services = services;
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

    public boolean needVarDeclaration(String propertyName) {
        return false;
    }


    public boolean canHandleReceiver(SLExpression receiver) {
        return receiver != null && receiver.isCollection();
    }


    protected SLExpression doResolving(SLExpression receiver,
                                       String name,
                                       SLParameters parameters)
                                   throws SLTranslationException {
        
        if(parameters == null
                || !(parameters instanceof OCLParameters)
                || !((OCLParameters)parameters).getDeclaredVars().isEmpty()) {
            return null;
        }

        String containingName;
        String propertyName = name;
        
        if(isFullyQualified(name)) {
            containingName = extractTypeName(name);
            propertyName = extractPropertyName(name);
        } else {
            KeYJavaType containingType = receiver.getKeYJavaType(javaInfo);
            if(containingType == null) {
                return null;
            }
            containingName = containingType.getFullName();
        }
        
        Term[] args 
            = fbc.convertFormulasToBool(((OCLParameters)parameters).getEntities()).toArray();
           
        OCLCollection recCollection = (OCLCollection) receiver.getCollection();       

        try {
            Term recVarTerm = recCollection.getPredVarAsTerm();
            Term methodTerm = javaInfo.getProgramMethodTerm(
                            recVarTerm,
                            propertyName,
                            args,
                            containingName);
            OCLCollection newCollection 
                    = recCollection.collect(services, methodTerm);
            return new OCLExpression(newCollection);
        } catch (IllegalArgumentException e) {
            return null;
        }

    }

}

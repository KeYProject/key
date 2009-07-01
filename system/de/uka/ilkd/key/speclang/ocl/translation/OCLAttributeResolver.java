// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
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

package de.uka.ilkd.key.speclang.ocl.translation;

import de.uka.ilkd.key.explicitheap.ExplicitHeapConverter;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.speclang.translation.SLResolverManager;
import de.uka.ilkd.key.speclang.translation.SLExpression;
import de.uka.ilkd.key.speclang.translation.SLExpressionResolver;
import de.uka.ilkd.key.speclang.translation.SLParameters;
import de.uka.ilkd.key.speclang.translation.SLTranslationException;


/**
 * Resolves attribute accesses.
 */
class OCLAttributeResolver extends SLExpressionResolver {
    
    
    public OCLAttributeResolver(Services services, SLResolverManager manager) {
        super(services.getJavaInfo(), manager);
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
        
        if(parameters != null) {
            return null;
        }
        
        ProgramVariable attribute;
        
        try{
        
            //try as fully qualified name
            attribute = javaInfo.getAttribute(name);
        } catch(IllegalArgumentException e){
            
            //try as short name
            KeYJavaType containingType = receiver.getKeYJavaType(javaInfo);
            attribute = javaInfo.lookupVisibleAttribute(name, containingType);
        }
        
        if(attribute != null) {
            OCLCollection recCollection = (OCLCollection) receiver.getCollection();
            
            Term recVarTerm = recCollection.getPredVarAsTerm();
            Function fieldSymbol = ExplicitHeapConverter.INSTANCE.getFieldSymbol(attribute, services);
            Term attributeTerm = TB.dot(services, attribute.sort(), recVarTerm, fieldSymbol); 
            OCLCollection newCollection 
                    = recCollection.collect(services, attributeTerm);
            return new OCLExpression(newCollection);
        }   
    
        return null;
    }    
}

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
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.util.AssertionFailure;


/**
 * Resolves attribute accesses.
 */
class AttributeResolver implements PropertyResolver {
    
    private static final TermFactory tf = TermFactory.DEFAULT;
    private final Services services;
    private final JavaInfo javaInfo;
    
    public AttributeResolver(Services services) {
        this.services = services;
        this.javaInfo = services.getJavaInfo();
    }
    
    
    public OCLEntity resolve(OCLEntity receiver,
                             String name, 
                             OCLParameters parameters) throws OCLTranslationError {
        if(parameters != null) {
            return null;
        }
        
        ProgramVariable attribute;
        try{
            //try as fully qualified name
            attribute = javaInfo.getAttribute(name);
        } catch(IllegalArgumentException e){
            //try as short name
            KeYJavaType containingType 
                      = javaInfo.getKeYJavaType(receiver.getSort());
            attribute = javaInfo.lookupVisibleAttribute(name, containingType);
        }
        
        if(attribute != null) {
            Term recTerm                = receiver.getTerm();
            KeYJavaType recType         = receiver.getType();
            OCLCollection recCollection = receiver.getCollection();
            
            try {
                if(recTerm != null || recType != null) {
                    Term attributeTerm = tf.createAttributeTerm(attribute, 
                                                                recTerm);
                    return new OCLEntity(attributeTerm);
                } else if(recCollection != null) {
                    Term recVarTerm = recCollection.getPredVarAsTerm();
                    Term attributeTerm = tf.createAttributeTerm(attribute, 
                                                                recVarTerm);                
                    OCLCollection newCollection 
                            = recCollection.collect(services, attributeTerm);
                    return new OCLEntity(newCollection);
                }
            } catch(Exception e) {
            	if (e instanceof OCLTranslationError) {
            		throw (OCLTranslationError) e;
            	}
            }
        }   
    
        return null;
    }

    
    public boolean needVarDeclaration(String propertyName) {
        return false;
    }    
}

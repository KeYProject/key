// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.speclang.ocl.translation;

import de.uka.ilkd.key.casetool.Association;
import de.uka.ilkd.key.casetool.ListOfAssociation;
import de.uka.ilkd.key.casetool.UMLInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.sort.AbstractCollectionSort;
import de.uka.ilkd.key.speclang.translation.SLResolverManager;
import de.uka.ilkd.key.speclang.translation.SLExpression;
import de.uka.ilkd.key.speclang.translation.SLExpressionResolver;
import de.uka.ilkd.key.speclang.translation.SLParameters;
import de.uka.ilkd.key.speclang.translation.SLTranslationException;


/**
 * Resolves association accesses.
 */
class AssociationResolver extends SLExpressionResolver {
    
    private static final TermFactory tf = TermFactory.DEFAULT;
    private final Services services;
    private final UMLInfo umlInfo;
    
    
    public AssociationResolver(Services services, SLResolverManager man) {
        super(services.getJavaInfo(), man);
        this.services = services;
        this.umlInfo  = services.getUMLInfo();
    }
    
    
    private static Function getAssociationFunction(Association assoc, 
	    					   String name) {        
        Function assocFunction1 = assoc.getFunction1();
        Function assocFunction2 = assoc.getFunction2();
        
        if(assocFunction1 != null && assocFunction2 != null) {
            assert assocFunction1.arity() == 1
                   && assocFunction2.arity() == 1;
    
            return (assocFunction1.name().toString().equals(name)
                    ? assocFunction1
                    : assocFunction2); 
        }
        
        return assoc.getPredicate();
    }
    
  
    public boolean needVarDeclaration(String propertyName) {
        return false;
    }


    public boolean canHandleReceiver(SLExpression receiver) {
        return receiver != null && (receiver.isTerm() || receiver.isCollection());
    }


    public SLExpression doResolving(SLExpression receiver,
                                    String name,
                                    SLParameters parameters)
                                throws SLTranslationException {        
        if(parameters != null) {
            return null;
        }
        
        KeYJavaType containingKjt = receiver.getKeYJavaType(javaInfo);
        ListOfAssociation assocs = umlInfo.getAssociations(containingKjt, name);
        
        if(!assocs.isEmpty()) {            
            Term recTerm                = receiver.getTerm();
            OCLCollection recCollection = (OCLCollection) receiver.getCollection();

            Association assoc = assocs.head();
            Function assocFunc = getAssociationFunction(assoc, name);

            if(recTerm != null) {                    
                if (assocFunc.sort() instanceof AbstractCollectionSort) {
                    // we have a binary association with multiplicity greater than 1
                    OCLCollection collection = new OCLCollection(recTerm,assoc,name);
                    return new OCLEntity(collection);
                } else {
                    // either the association-end has multiplicity 1 or it is no binary association
                    Term functionTerm = tf.createFunctionTerm(assocFunc,recTerm);
                    return new OCLEntity(functionTerm);
                }
            } else if(recCollection != null) {
                OCLCollection newCollection
                        = recCollection.collect(services,
                                                assoc,
                                                name);
                return new OCLEntity(newCollection);
            }
        } 
        
        return null;
    }
}       

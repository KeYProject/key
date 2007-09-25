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

import de.uka.ilkd.key.casetool.Association;
import de.uka.ilkd.key.casetool.ListOfAssociation;
import de.uka.ilkd.key.casetool.UMLInfo;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.sort.AbstractCollectionSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.util.Debug;
import de.uka.ilkd.key.util.AssertionFailure;


/**
 * Resolves association accesses.
 */
class AssociationResolver implements PropertyResolver {
    
    private static final TermFactory tf = TermFactory.DEFAULT;
    private final Services services;
    private final JavaInfo javaInfo;
    private final UMLInfo umlInfo;
    
    
    public AssociationResolver(Services services) {
        this.services = services;
        this.javaInfo = services.getJavaInfo();
        this.umlInfo  = services.getUMLInfo();
        assert javaInfo != null;
        assert umlInfo != null;
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
    
    
    public OCLEntity resolve(OCLEntity receiver,
                             String name, 
                             OCLParameters parameters) throws OCLTranslationError {
        if(parameters != null) {
            return null;
        }
        
        Sort containingSort = receiver.getSort();
        KeYJavaType containingKjt = javaInfo.getKeYJavaType(containingSort);
        ListOfAssociation assocs = umlInfo.getAssociations(containingKjt, name);
        
        if(!assocs.isEmpty()) {            
            Term recTerm                = receiver.getTerm();
            OCLCollection recCollection = receiver.getCollection();

            Association assoc = assocs.head();
            Function assocFunc = getAssociationFunction(assoc, name);

            try {
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

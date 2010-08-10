// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.speclang.ocl.translation;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.speclang.ocl.Association;
import de.uka.ilkd.key.speclang.translation.SLCollection;
import de.uka.ilkd.key.speclang.translation.SLTranslationException;

/**
 * This class represents the CollectionType of OCL.
 * 
 */
class OCLCollection extends SLCollection{
    
    public static final int OCL_SET = 0;
    public static final int OCL_BAG = 1;
    public static final int OCL_SEQUENCE = 2;
    
    private final OCLPredicativeCollection predInterpretation;
    private final OCLFunctionalCollection funcInterpretation;
    

    /**
     * Creates a collection which contains all values of a sort which satisfy 
     * some restriction. Functional and predicative interpretation are explicitly given.
     * 
     * @param var
     * @param pRestriction predicative restriction
     * @param fRestriction functional restriction
     * @param collectionType type of this Collection
     */
    private OCLCollection(LogicVariable var, 
                         Term pRestriction,
                         Term fRestriction,
                         int collectionType) {
        predInterpretation = new OCLPredicativeCollection(var,pRestriction);
        funcInterpretation = new OCLFunctionalCollection(fRestriction,collectionType);
    }
    

    /**
     * Creates an empty collection of type <b>collectionType</b>.
     */
    public OCLCollection(int collectionType) {
        predInterpretation = new OCLPredicativeCollection();
        funcInterpretation = new OCLFunctionalCollection(collectionType);
    }
    
    
    /**
     * Creates an empty set.
     */
    public OCLCollection() {
        this(OCL_SET);
    }

    
    /**
     * Creates a set which contains all values of a sort which are not null.
     */
    public OCLCollection(Sort sort, Services services) {
        this(sort,OCL_SET, services);
    }


    /**
     * Creates a collection which contains all values of a sort which are not null
     */
    public OCLCollection(Sort sort, int collectionType, Services services) {
        predInterpretation = new OCLPredicativeCollection(sort, services);
        funcInterpretation = new OCLFunctionalCollection(sort,collectionType);
    }

    
    /**
     * Creates a collection which contains a single element.
     * @throws SLTranslationException 
     */
    public OCLCollection(Term element, int collectionType) throws SLTranslationException {
        predInterpretation = new OCLPredicativeCollection(element);
        funcInterpretation = new OCLFunctionalCollection(collectionType, element);
    }
    
    
    /**
     * Creates a set which contains a single element.
     * @throws SLTranslationException 
     */
    public OCLCollection(Term element) throws SLTranslationException {
        this(element, OCL_SET);
    }
    

    /**
     * Creates a collection which contains all integers between a lower and
     * an upper bound (described by terms of sort int).
     * @throws SLTranslationException 
     */
    public OCLCollection(Term lowerBound, 
                         Term upperBound, 
                         Function leq,
                         int collectionType) throws SLTranslationException {
        predInterpretation = new OCLPredicativeCollection(lowerBound,upperBound,leq);
        funcInterpretation = new OCLFunctionalCollection(lowerBound,upperBound,leq,collectionType);
    }
    
    
    /**
     * Creates a set which contains all integers between a lower and
     * an upper bound (described by terms of sort int).
     * @throws SLTranslationException 
     */
    public OCLCollection(Term lowerBound, 
                         Term upperBound, 
                         Function leq) throws SLTranslationException {
        this(lowerBound,upperBound,leq,OCL_SET);
    }
    
    
    /**
     * Creates a collection which contains all values reachable from a receiver 
     * term by applying an association with multiplicity > 1 (described by a 
     * predicate).
     */
    public OCLCollection(Term recTerm,
                         Association assoc,
                         String name) {
        predInterpretation = new OCLPredicativeCollection(recTerm,assoc.getPredicate());
        funcInterpretation = new OCLFunctionalCollection(
                recTerm,
                getAssociationFunction(assoc, name));
    }
    
    
    private OCLCollection(OCLPredicativeCollection pc, OCLFunctionalCollection fc) {
        this.predInterpretation = pc;
        this.funcInterpretation = fc;
    }
    
    
    public LogicVariable getPredVar() {
        return predInterpretation.getVar();
    }
    
    
    public Term getPredVarAsTerm() {
        return predInterpretation.getVarAsTerm();
    }
    
    
    public Sort getElementSort() {
        return predInterpretation.getSort();
    }
    
    
    public int getCollectionType() {
        return funcInterpretation.getCollectionType();
    }
    
    
    public Term getFunctionalRestriction() {
        return funcInterpretation.getRestriction();
    }
    
    
    public Term getPredicativeRestriction() {
        return predInterpretation.getRestriction();
    }
    

    public boolean isSet() {
    	return funcInterpretation.isSet();
    }
    

    public boolean isBag() {
    	return funcInterpretation.isBag();
    }
    

    public boolean isSequence() {
    	return funcInterpretation.isSequence();
    }
    

    public String toString() {
        return "OCLCollection\npredicative: " + predInterpretation + "\nfunctional: " + funcInterpretation + "\n";
    }
    
    
    /**
     * Creates a collection which is the union of this one and another one.
     * 
     * @param c collection to union with
     * @return Collection containing all the elements from <b>this</b> and <b>c</b>
     * @throws SLTranslationException 
     */
    public OCLCollection union(OCLCollection c) throws SLTranslationException {
        return new OCLCollection(
                getPredVar(),
                predInterpretation.union(c).getRestriction(),
                funcInterpretation.union(c).getRestriction(),
                getCollectionType());
    }
    

    /**
     * Creates the collection which results from the call
     * c->collect(b|e) alias c->collect(e) or c.e
     * where c is <b>this</b>
     * 
     * @param services global services
     * @param collectTerm e
     * @return the appropriate collection
     * @throws SLTranslationException 
     */
    public OCLCollection collect(Services services, Term collectTerm) throws SLTranslationException {
        
        OCLPredicativeCollection pc = predInterpretation.navigate(services, collectTerm);
        OCLFunctionalCollection fc = funcInterpretation.collect(collectTerm);
        
        return new OCLCollection(pc,fc);
    }


    /**
     * Creates the collection which results from applying an association
     * to this collection
     * 
     * @param services global services
     * @param assoc the Association over which is navigated
     * @return the appropriate collection (hopefully) :)
     * @throws SLTranslationException 
     */
    public OCLCollection collect(Services services,
                                 Association assoc,
                                 String name)
                             throws SLTranslationException {
        
        Function assocFunc = getAssociationFunction(assoc, name);
        
        // This should be allowed!
        //if (assocFunc.sort() instanceof AbstractCollectionSort) {
            //result would be a set of sets => not supported!
        //    Debug.fail("OCLCollection: Sets of sets are not supported!");
        //    return null;
        //}
        
        OCLPredicativeCollection pc = predInterpretation.navigate(services, assoc.getPredicate());
        OCLFunctionalCollection fc = funcInterpretation.collect(
                TermFactory.DEFAULT.createFunctionTerm(assocFunc,getPredVarAsTerm()));
        
        return new OCLCollection(pc,fc);
    }

    
    /**
     * Creates the flattened collection which results from applying an association
     * to this collection (described by a OCLCollection)
     * 
     * @param services global services
     * @param collection the applied association
     * @return the appropriate collection (hopefully) :)
     */
	public OCLCollection collect(Services services, OCLCollection collection) {
		// TODO Auto-generated method stub
		return null;
	}

	
    /**
     * Creates the collection which results from the call
     * c->select(b|e) alias c->select(e)
     * 
     * @param selectVar variable used in e for referring to the instances of c
     * @param selectTerm e
     * @return the appropriate collection
     * @throws SLTranslationException 
     */
    public OCLCollection select(LogicVariable selectVar, Term selectTerm) throws SLTranslationException {
        
        OCLPredicativeCollection pc = predInterpretation.narrow(selectTerm);
        OCLFunctionalCollection fc = funcInterpretation.select(selectVar, selectTerm);
        
        return new OCLCollection(pc,fc);
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


    public static OCLCollection convertToOCLCollection(SLCollection c) {
        
        if (c instanceof OCLCollection) {
            return (OCLCollection) c;
        }
        
        // TODO ... sometime in the future if this is needed. For now
        // the only collections existing are OCLCollections.
        return new OCLCollection();
    
    }

}

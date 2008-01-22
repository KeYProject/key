// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.speclang.ocl.translation;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.SetOfQuantifiableVariable;
import de.uka.ilkd.key.logic.sort.SequenceSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.speclang.translation.SLTranslationException;
import de.uka.ilkd.key.util.Debug;

class OCLFunctionalCollection {
    
    private static final TermFactory tf = TermFactory.DEFAULT;
    private static final FunctionFactory funcFactory = FunctionFactory.INSTANCE;
    private final Term restriction;
    
    private final int collectionType;
    
    /**
     * Creates a collection of Type <b>collectionType</b> which contains 
     * all values of a sort which satisfy some restriction. (functional)
     */
    protected OCLFunctionalCollection(Term restriction,
                         int collectionType) {
        this.restriction = restriction;
        this.collectionType = collectionType;
    }
    
    /**
     * Creates an empty collection.
     */
    protected OCLFunctionalCollection() {
        this(OCLCollection.OCL_SET);
    }
    
    /**
     * Creates an empty collection.
     */
    protected OCLFunctionalCollection(int collectionType) {
        this.restriction = tf.createFunctionTerm(funcFactory.getEmptySet(Sort.ANY)); 
        this.collectionType = collectionType;
    }
    
    /**
     * Creates a collection which contains all values of a sort.
     */
    protected OCLFunctionalCollection(Sort sort, int collectionType) {
        this.restriction = tf.createFunctionTerm(
                funcFactory.createAllInstancesConstant(sort));
        this.collectionType = collectionType;
    }

    
    /**
     * Creates a collection which contains all values of a sort.
     */
    protected OCLFunctionalCollection(Sort sort) {
        this(sort,OCLCollection.OCL_SET);
    }
    

    /**
     * Creates a collection which contains a single element.
     * @throws SLTranslationException 
     */
    protected OCLFunctionalCollection(int collectionType, Term element) throws SLTranslationException {
        this.restriction = funcFactory.including(
                tf.createFunctionTerm(funcFactory.getEmptySet(element.sort())),
                element);
        this.collectionType = collectionType;
    }
    
    
    /**
     * Creates a collection which contains a single element.
     * @throws SLTranslationException 
     */
    protected OCLFunctionalCollection(Term element) throws SLTranslationException {
        this(OCLCollection.OCL_SET,element);
    }

    
    /**
     * Creates a collection which contains all integers between a lower and
     * an upper bound (described by terms of sort int).
     * @throws SLTranslationException 
     */
    protected OCLFunctionalCollection(Term lowerBound, 
                         Term upperBound, 
                         Function leq,
                         int collectionType) throws SLTranslationException {
        switch (collectionType) {
            case OCLCollection.OCL_SET : 
                this.restriction = funcFactory.createRangedSet(lowerBound,upperBound,leq);
                break;
            case OCLCollection.OCL_BAG :
                this.restriction = funcFactory.createRangedBag(lowerBound,upperBound,leq);
                break;
            case OCLCollection.OCL_SEQUENCE :
                this.restriction = funcFactory.createRangedSequence(lowerBound,upperBound,leq);
                break;
            default:
                this.restriction = funcFactory.createRangedSet(lowerBound,upperBound,leq);
        }
        this.collectionType = collectionType;
    }
    
    
    /**
     * Creates a collection which contains all integers between a lower and
     * an upper bound (described by terms of sort int).
     * @throws SLTranslationException 
     */
    protected OCLFunctionalCollection(Term lowerBound, 
                         Term upperBound, 
                         Function leq) throws SLTranslationException {
        this(lowerBound,upperBound,leq,OCLCollection.OCL_SET);
    }

    
    /**
     * Creates a collection which contains all values reachable from a receiver 
     * term by applying an association with multiplicity > 1 (described by an
     * association-function).
     */
    protected OCLFunctionalCollection(Term recTerm, 
                         Function assocFunc) {
        Debug.assertTrue(assocFunc!=null);
        assert assocFunc!=null;
        Debug.assertTrue(assocFunc.arity()==1);
        Debug.assertTrue(assocFunc.argSort(0)==recTerm.sort());
        this.restriction = tf.createFunctionTerm(assocFunc,recTerm);
        this.collectionType = 
            (assocFunc.sort() instanceof SequenceSort) ? 
                    OCLCollection.OCL_SEQUENCE : OCLCollection.OCL_SET;
    }
    
    
    public Term getRestriction() {
        return restriction;
    }
    
    
    protected int getCollectionType() {
        return collectionType;
    }
    
    
    public boolean isSet() {
    	return collectionType == OCLCollection.OCL_SET;
    }
    

    public boolean isBag() {
    	return collectionType == OCLCollection.OCL_BAG;
    }
    
    
    public boolean isSequence() {
    	return collectionType == OCLCollection.OCL_SEQUENCE;
    }
    

    public String toString() {
        return "(all elements of " + restriction.sort() + " in " + restriction + ")";
    }
    
    
    /**
     * Creates a collection which is the union of this one and another one.
     * @throws SLTranslationException 
     */
    protected OCLFunctionalCollection union(OCLCollection c) throws SLTranslationException {
        return new OCLFunctionalCollection(
                funcFactory.unionAndSimplify(
                        this.restriction,
                        c.getFunctionalRestriction()),
                this.collectionType);
    }

    
    /**
     * Creates a functional description of a collection which is produced by
     * e->collect(b)
     * 
     * @param collectTerm b
     * @return new functional description of the appropriate collection
     * @throws SLTranslationException 
     */
    public OCLFunctionalCollection collect(Term collectTerm)
                               throws SLTranslationException {

        // is this right? 
        // or are there any collect-expressions which don't have the collectorVar as first subterm?
        LogicVariable collectVar = (LogicVariable) collectTerm.sub(0).freeVars().toArray()[0];
        
        Function f = funcFactory.createCollectFunction(
                collectVar,
                collectTerm,
                this.collectionType);

        SetOfQuantifiableVariable vars = collectTerm.freeVars();
        vars = vars.remove(collectVar);
        
        Term[] params = new Term[vars.size()+1];
        
        params[0] = this.restriction;
        
        for(int i=0;i<vars.size();i++) {
            params[i+1] = tf.createVariableTerm((LogicVariable) vars.toArray()[i]);
        }
        
        Term newRestriction = tf.createFunctionTerm(f,params);

        int newCollectionType = (this.collectionType == OCLCollection.OCL_SEQUENCE) ? 
                OCLCollection.OCL_SEQUENCE : OCLCollection.OCL_BAG;
        
        return new OCLFunctionalCollection(newRestriction,newCollectionType);
    }
    
    
    /**
     * Creates a functional description of a collection which is produced by
     * e->select(x | b)
     * 
     * @param selectVar x
     * @param selectTerm b
     * @return new functional description of the appropriate collection
     * @throws SLTranslationException 
     */
    public OCLFunctionalCollection select(LogicVariable selectVar, Term selectTerm) throws SLTranslationException {
        
        Function f = funcFactory.createSelectFunction(
                selectVar,
                selectTerm,
                this.collectionType);                

        SetOfQuantifiableVariable vars = selectTerm.freeVars();
        vars = vars.remove(selectVar);
        
        Term[] params = new Term[vars.size()+1];
        
        params[0] = this.restriction;
        
        for(int i=0;i<vars.size();i++) {
            params[i+1] = tf.createVariableTerm((LogicVariable) vars.toArray()[i]);
        }
        
        Term newRestriction = tf.createFunctionTerm(f,params);

        return new OCLFunctionalCollection(newRestriction,this.collectionType);
    }
    
}

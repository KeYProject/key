// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.speclang;

import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.Map;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.logic.SetAsListOfLocationDescriptor;
import de.uka.ilkd.key.logic.SetAsListOfTerm;
import de.uka.ilkd.key.logic.SetOfLocationDescriptor;
import de.uka.ilkd.key.logic.SetOfTerm;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.proof.AtPreFactory;
import de.uka.ilkd.key.proof.OpReplacer;


/**
 * Standard implementation of the LoopInvariant interface.
 */
public class LoopInvariantImpl implements LoopInvariant {
    
    private final LoopStatement loop;
    private final Term originalInvariant;
    private final Term originalWorkingSpace;
    private final SetOfTerm originalPredicates;
    private final SetOfLocationDescriptor originalModifies;
    private final Term originalVariant;
    private final Term originalSelfTerm;
    private final Map<Operator, Function /*(atPre)*/> originalAtPreFunctions;
    private final boolean predicateHeuristicsAllowed;
    
    
    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------
    
    /**
     * Creates a loop invariant.
     * @param loop the loop to which the invariant belongs
     * @param invariant the invariant formula
     * @param predicates the loop predicates
     * @param modifies the modifier set
     * @param variant the variant term
     * @param selfTerm the term used for the receiver object
     * @param atPreFunctions the functions used for atPre
     * @param predicateHeuristicsAllowed whether heuristics for generating
     *        additional loop predicates are allowed
     */
    public LoopInvariantImpl(LoopStatement loop,
                             Term invariant,
                             SetOfTerm predicates,
                             SetOfLocationDescriptor modifies,  
                             Term variant, 
                             Term workingSpace,
                             Term selfTerm,
                             /*in*/ Map<Operator, Function /*(atPre)*/> atPreFunctions,
                             boolean predicateHeuristicsAllowed) {
        assert loop != null;
        assert predicates != null;
        assert modifies != null;
        assert atPreFunctions != null;
        this.loop                       = loop;
	this.originalInvariant          = invariant;
        this.originalPredicates         = predicates;
        this.originalVariant            = variant;
        this.originalWorkingSpace       = workingSpace;
        this.originalModifies           = modifies;
        this.originalSelfTerm           = selfTerm;   
        this.predicateHeuristicsAllowed = predicateHeuristicsAllowed;
        this.originalAtPreFunctions     = new LinkedHashMap<Operator, Function>();
        this.originalAtPreFunctions.putAll(atPreFunctions);
    }
    
    
    /**
     * Creates an empty, default loop invariant for the passed loop.
     */
    public LoopInvariantImpl(LoopStatement loop, Term selfTerm) {
        this(loop, 
             null, 
             SetAsListOfTerm.EMPTY_SET, 
             SetAsListOfLocationDescriptor.EMPTY_SET, 
             null, 
             null,
             selfTerm,
             new LinkedHashMap<Operator, Function>(),
             true);
    }
    
    
    
    //-------------------------------------------------------------------------
    //internal methods
    //-------------------------------------------------------------------------
    
    private Map /*Operator, Operator, Term -> Term*/ getReplaceMap(
            Term selfTerm,
            /*inout*/ Map<Operator, Function/*atpre*/> atPreFunctions,
            Services services) {
        Map result = new LinkedHashMap();
        
        //self
        if(selfTerm != null) {
            assert selfTerm.sort().extendsTrans(originalSelfTerm.sort());
            result.put(originalSelfTerm, selfTerm);
        }
        
        //-parameters and other local variables are always kept up to
        // date by the ProgVarReplaceVisitor

        //atPre-functions
        if(atPreFunctions != null) {
            Iterator<Map.Entry<Operator, Function>> it = 
                originalAtPreFunctions.entrySet().iterator();
            while(it.hasNext()) {
                Map.Entry<Operator, Function> entry = it.next();
                Operator originalNormalOp = entry.getKey();
                Function originalAtPreFunc = entry.getValue();
                Operator normalOp = (Operator) result.get(originalNormalOp);
                if(normalOp == null) {
                    normalOp = originalNormalOp;
                }
                Function atPreFunc = atPreFunctions.get(normalOp);
                if(atPreFunc == null) {
                    atPreFunc 
                        = AtPreFactory.INSTANCE.createAtPreFunction(normalOp, 
                                                                    services);
                    atPreFunctions.put(normalOp, atPreFunc);
                    services.getNamespaces().functions().add(atPreFunc);                    
                }
                assert originalAtPreFunc.sort().equals(atPreFunc.sort());
                result.put(originalAtPreFunc, atPreFunc);
            }
        }
        
        return result;
    }
    
    
    private Map /*Term -> Term*/ getInverseReplaceMap(
            Term selfTerm,
            /*inout*/ Map <Operator, Function/* atPre*/> atPreFunctions,
            Services services) {
       Map result = new LinkedHashMap();
       Map replaceMap = getReplaceMap(selfTerm, atPreFunctions, services);
       final Iterator<Map.Entry> it = replaceMap.entrySet().iterator();
       while(it.hasNext()) {
           Map.Entry entry = it.next();
           result.put(entry.getValue(), entry.getKey());
       }
       return result;
    }
    
    
    
    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------

    public LoopStatement getLoop() {
        return loop;
    }

    
    public Term getInvariant(Term selfTerm,
            /*inout*/Map <Operator, Function/* (atPre)*/> atPreFunctions,
            Services services) {
        assert (selfTerm == null) == (originalSelfTerm == null);
        Map replaceMap = getReplaceMap(selfTerm, atPreFunctions, services);
        OpReplacer or = new OpReplacer(replaceMap);
        return or.replace(originalInvariant);
    }
    
    
    public SetOfTerm getPredicates(Term selfTerm,
            /*inout*/ Map<Operator, Function/* (atPre)*/> atPreFunctions,
            Services services) {
        assert (selfTerm == null) == (originalSelfTerm == null);
        Map replaceMap = getReplaceMap(selfTerm, atPreFunctions, services);
        OpReplacer or = new OpReplacer(replaceMap);
        return or.replace(originalPredicates);
    }

    
    public SetOfLocationDescriptor getModifies(
            Term selfTerm,
            /*inout*/ Map<Operator, Function/* (atPre)*/> atPreFunctions,
            Services services) {
        assert (selfTerm == null) == (originalSelfTerm == null);
        Map replaceMap = 
            getReplaceMap(selfTerm, atPreFunctions, services);
        OpReplacer or = new OpReplacer(replaceMap);
        return or.replace(originalModifies);
    }
    

    public Term getVariant(Term selfTerm, 
            /*inout*/ Map <Operator, Function/* (atPre)*/> atPreFunctions,
            Services services) {
        assert (selfTerm == null) == (originalSelfTerm == null);
        Map replaceMap = 
            getReplaceMap(selfTerm, atPreFunctions, services);
        OpReplacer or = new OpReplacer(replaceMap);
        return or.replace(originalVariant);
    }
    
    public Term getWorkingSpace(Term selfTerm, 
            /*inout*/ Map <Operator, Function/* (atPre)*/> atPreFunctions,
            Services services){
        assert (selfTerm == null) == (originalSelfTerm == null);
        Map replaceMap = 
            getReplaceMap(selfTerm, atPreFunctions, services);
        OpReplacer or = new OpReplacer(replaceMap);
        return or.replace(originalWorkingSpace);   
    }
    
    
    public boolean getPredicateHeuristicsAllowed() {
        return predicateHeuristicsAllowed;
    }
    
    
    public Term getInternalSelfTerm() {
        return originalSelfTerm;
    }
    
    
    public Map<Operator, Function> /*Operator (normal) -> Function (atPre)*/ 
                                                getInternalAtPreFunctions() {
        Map<Operator, Function> result = new LinkedHashMap<Operator, Function>();
        result.putAll(originalAtPreFunctions);
        return result;
    }
    
    
    public LoopInvariant setLoop(LoopStatement loop) {
        return new LoopInvariantImpl(loop,
                                     originalInvariant,
                                     originalPredicates,
                                     originalModifies,
                                     originalVariant,
                                     originalWorkingSpace,
                                     originalSelfTerm,
                                     originalAtPreFunctions,
                                     predicateHeuristicsAllowed);
    }
    
    
    public LoopInvariant setInvariant(Term invariant, 
            Term selfTerm,
            /*inout*/ Map <Operator, Function/* (atPre)*/> atPreFunctions,
            Services services) {
        assert (selfTerm == null) == (originalSelfTerm == null);
        Map inverseReplaceMap 
            = getInverseReplaceMap(selfTerm, atPreFunctions, services);
        OpReplacer or = new OpReplacer(inverseReplaceMap);
        return new LoopInvariantImpl(loop, 
                                     or.replace(invariant), 
                                     originalPredicates,  
                                     originalModifies, 
                                     originalVariant,
                                     originalWorkingSpace, 
                                     originalSelfTerm,
                                     originalAtPreFunctions,
                                     predicateHeuristicsAllowed);
    }
    

    public LoopInvariant setPredicates(SetOfTerm predicates, 
            Term selfTerm,
            /*inout*/ Map <Operator, Function/* atPre */> atPreFunctions,
            Services services) {
        assert (selfTerm == null) == (originalSelfTerm == null);
        Map inverseReplaceMap 
            = getInverseReplaceMap(selfTerm, atPreFunctions, services);
        OpReplacer or = new OpReplacer(inverseReplaceMap);
        return new LoopInvariantImpl(loop,
                                     originalInvariant,
                                     or.replace(predicates),
                                     originalModifies,
                                     originalVariant,
                                     originalWorkingSpace,
                                     originalSelfTerm,
                                     originalAtPreFunctions,
                                     predicateHeuristicsAllowed);
    }
    
    
    public LoopInvariant setPredicateHeuristicsAllowed(
                                        boolean predicateHeuristicsAllowed) {
        return new LoopInvariantImpl(loop,
                                     originalInvariant,
                                     originalPredicates,
                                     originalModifies,
                                     originalVariant,
                                     originalWorkingSpace,
                                     originalSelfTerm,
                                     originalAtPreFunctions,
                                     predicateHeuristicsAllowed);
    }
    
    
    public void visit(Visitor v) {
        v.performActionOnLoopInvariant(this);
    }
    
    
    public String toString() {
        return "invariant: " 
                + originalInvariant 
                + "; predicates: " 
                + originalPredicates 
                + "; modifies: " 
                + originalModifies
                + "; variant: "
                + originalVariant;
    }
}

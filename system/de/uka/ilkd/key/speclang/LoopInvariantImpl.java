// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
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

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.proof.OpReplacer;


/**
 * Standard implementation of the LoopInvariant interface.
 */
public final class LoopInvariantImpl implements LoopInvariant {
        
    private final LoopStatement loop;
    private final Term originalInvariant;
    private final LoopPredicateSet originalPredicates;
    private final Term originalModifies;
    private final Term originalVariant;
    private final Term originalSelfTerm;
    private final Term originalHeapAtPre;
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
     * @param heapAtPre the term used for the at pre heap
     * @param predicateHeuristicsAllowed whether heuristics for generating
     *        additional loop predicates are allowed
     */
    public LoopInvariantImpl(LoopStatement loop,
                             Term invariant,
                             LoopPredicateSet predicates,
                             Term modifies,  
                             Term variant, 
                             Term selfTerm,
                             Term heapAtPre,
                             boolean predicateHeuristicsAllowed) {
        assert loop != null;
        assert predicates != null;
        assert modifies != null;
        assert heapAtPre != null;
        this.loop                       = loop;
	this.originalInvariant          = invariant;
        this.originalPredicates         = predicates;
        this.originalVariant            = variant;
        this.originalModifies           = modifies;
        this.originalSelfTerm           = selfTerm;   
        this.predicateHeuristicsAllowed = predicateHeuristicsAllowed;
        this.originalHeapAtPre          = heapAtPre;
    }
    
    
    /**
     * Creates an empty, default loop invariant for the passed loop.
     */
    public LoopInvariantImpl(LoopStatement loop, 
	    		     Term selfTerm, 
	    		     Term heapAtPre) {
        this(loop, 
             null, 
             new LoopPredicateSet(DefaultImmutableSet.<Term>nil()), 
             null, 
             null, 
             selfTerm,
             null,
             true);
    }
    
    
    
    //-------------------------------------------------------------------------
    //internal methods
    //-------------------------------------------------------------------------
    
    private Map /*Operator, Operator, Term -> Term*/ getReplaceMap(
            Term selfTerm,
            Term heapAtPre,
            Services services) {
        Map result = new LinkedHashMap();
        
        //self
        if(selfTerm != null) {
            assert selfTerm.sort().extendsTrans(originalSelfTerm.sort());
            result.put(originalSelfTerm, selfTerm);
        }
        
        //-parameters and other local variables are always kept up to
        // date by the ProgVarReplaceVisitor

        //atPre heap
        if(heapAtPre != null) {
	    assert originalHeapAtPre.sort().equals(heapAtPre.sort());
	    result.put(originalHeapAtPre, heapAtPre);
        }
        
        return result;
    }
    
    
    private Map /*Term -> Term*/ getInverseReplaceMap(
            Term selfTerm,
            Term heapAtPre,
            Services services) {
       Map result = new LinkedHashMap();
       Map replaceMap = getReplaceMap(selfTerm, heapAtPre, services);
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

    @Override
    public LoopStatement getLoop() {
        return loop;
    }

    
    @Override    
    public Term getInvariant(Term selfTerm,
            		     Term heapAtPre,
            		     Services services) {
        assert (selfTerm == null) == (originalSelfTerm == null);
        Map replaceMap = getReplaceMap(selfTerm, heapAtPre, services);
        OpReplacer or = new OpReplacer(replaceMap);
        return or.replace(originalInvariant);
    }
    
    
    public LoopPredicateSet getPredicates(Term selfTerm,
            Term heapAtPre,
            Services services) {
        assert (selfTerm == null) == (originalSelfTerm == null);
        Map replaceMap = getReplaceMap(selfTerm, heapAtPre, services);
        OpReplacer or = new OpReplacer(replaceMap);
        return new LoopPredicateSet(or.replace(originalPredicates.asSet()));
    }

    
    @Override
    public Term getModifies(Term selfTerm,
            		    Term heapAtPre,
            		    Services services) {
        assert (selfTerm == null) == (originalSelfTerm == null);
        Map replaceMap = 
            getReplaceMap(selfTerm, heapAtPre, services);
        OpReplacer or = new OpReplacer(replaceMap);
        return or.replace(originalModifies);
    }
    

    @Override
    public Term getVariant(Term selfTerm, 
            		   Term heapAtPre,
            		   Services services) {
        assert (selfTerm == null) == (originalSelfTerm == null);
        Map replaceMap = 
            getReplaceMap(selfTerm, heapAtPre, services);
        OpReplacer or = new OpReplacer(replaceMap);
        return or.replace(originalVariant);
    }
    
    
    @Override
    public boolean getPredicateHeuristicsAllowed() {
        return predicateHeuristicsAllowed;
    }
    
    
    @Override
    public Term getInternalSelfTerm() {
        return originalSelfTerm;
    }
    
    
    @Override
    public Term getInternalHeapAtPre() {
        return originalHeapAtPre;
    }
    
    
    @Override
    public LoopInvariant setLoop(LoopStatement loop) {
        return new LoopInvariantImpl(loop,
                                     originalInvariant,
                                     originalPredicates,
                                     originalModifies,
                                     originalVariant,
                                     originalSelfTerm,
                                     originalHeapAtPre,
                                     predicateHeuristicsAllowed);
    }
    
    
    @Override
    public LoopInvariant setInvariant(Term invariant, 
            			      Term selfTerm,
            			      Term heapAtPre,
            			      Services services) {
        assert (selfTerm == null) == (originalSelfTerm == null);
        Map inverseReplaceMap 
            = getInverseReplaceMap(selfTerm, heapAtPre, services);
        OpReplacer or = new OpReplacer(inverseReplaceMap);
        return new LoopInvariantImpl(loop, 
                                     or.replace(invariant), 
                                     originalPredicates,  
                                     originalModifies, 
                                     originalVariant, 
                                     originalSelfTerm,
                                     originalHeapAtPre,
                                     predicateHeuristicsAllowed);
    }
    

    public LoopInvariant setPredicates(ImmutableSet<Term> predicates, 
            Term selfTerm,
            Term heapAtPre,
            Services services) {
        assert (selfTerm == null) == (originalSelfTerm == null);
        Map inverseReplaceMap 
            = getInverseReplaceMap(selfTerm, heapAtPre, services);
        OpReplacer or = new OpReplacer(inverseReplaceMap);
        return new LoopInvariantImpl(loop,
                                     originalInvariant,
                                     new LoopPredicateSet(or.replace(predicates)),
                                     originalModifies,
                                     originalVariant,
                                     originalSelfTerm,
                                     originalHeapAtPre,
                                     predicateHeuristicsAllowed);
    }
    
    
    @Override
    public LoopInvariant setPredicateHeuristicsAllowed(
                                        boolean predicateHeuristicsAllowed) {
        return new LoopInvariantImpl(loop,
                                     originalInvariant,
                                     originalPredicates,
                                     originalModifies,
                                     originalVariant,
                                     originalSelfTerm,
                                     originalHeapAtPre,
                                     predicateHeuristicsAllowed);
    }
    
    
    @Override
    public void visit(Visitor v) {
        v.performActionOnLoopInvariant(this);
    }
    
    
    @Override
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

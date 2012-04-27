// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.speclang;

import java.util.LinkedHashMap;
import java.util.Map;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.modifier.VisibilityModifier;
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
    private final Term originalTransactionInvariant;
    private final Term originalModifies;
    private final Term originalModifiesBackup;
    private final Term originalVariant;
    private final Term originalSelfTerm;
    private final Term originalHeapAtPre;
    private final Term originalSavedHeapAtPre;
    
    
    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------
    
    /**
     * Creates a loop invariant.
     * @param loop the loop to which the invariant belongs
     * @param invariant the invariant formula
     * @param modifies the modifier set
     * @param variant the variant term
     * @param selfTerm the term used for the receiver object
     * @param heapAtPre the term used for the at pre heap
     */
    public LoopInvariantImpl(LoopStatement loop,
                             Term invariant,
                             Term transactionInvariant,
                             Term modifies,  
                             Term modifiesBackup,  
                             Term variant, 
                             Term selfTerm,
                             Term heapAtPre,
                             Term savedHeapAtPre) {
        assert loop != null;
        //assert modifies != null;
        //assert heapAtPre != null;
        this.loop                       = loop;
        this.originalInvariant          = invariant;
        this.originalTransactionInvariant = transactionInvariant;
        this.originalVariant            = variant;
        this.originalModifies           = modifies;
        this.originalModifiesBackup     = modifiesBackup;
        this.originalSelfTerm           = selfTerm;   
        this.originalHeapAtPre          = heapAtPre;
        this.originalSavedHeapAtPre     = savedHeapAtPre;
    }

    public LoopInvariantImpl(LoopStatement loop,
                             Term invariant,
                             Term modifies,   
                             Term variant, 
                             Term selfTerm,
                             Term heapAtPre) {
        this(loop,invariant,null,modifies,null,variant,selfTerm,heapAtPre,null);
    }
    
    /**
     * Creates an empty, default loop invariant for the passed loop.
     */
    public LoopInvariantImpl(LoopStatement loop, 
	    		     Term selfTerm, 
	    		     Term heapAtPre) {
        this(loop, 
             null, 
             null, 
             null,
             null,
             null,
             selfTerm,
             null,
             null);
    }
    
    
    
    //-------------------------------------------------------------------------
    //internal methods
    //-------------------------------------------------------------------------
    
    private Map /*Operator, Operator, Term -> Term*/<Term, Term> getReplaceMap(
            Term selfTerm,
            Term heapAtPre,
            Term savedHeapAtPre,
            Services services) {
        final Map<Term, Term> result = new LinkedHashMap<Term, Term>();
        
        //self
        if(selfTerm != null) {
//            assert selfTerm.sort().extendsTrans(originalSelfTerm.sort()) :
//        	   "instantiating sort " + originalSelfTerm.sort()
//        	   + " with sort " + selfTerm.sort()
//        	   + " which is not a subsort!";
            result.put(originalSelfTerm, selfTerm);
        }
        
        //-parameters and other local variables are always kept up to
        // date by the ProgVarReplaceVisitor

        //atPre heap
        if(heapAtPre != null) {
	    assert originalHeapAtPre.sort().equals(heapAtPre.sort());
	    result.put(originalHeapAtPre, heapAtPre);
        }

        if(savedHeapAtPre != null) {
            assert originalSavedHeapAtPre.sort().equals(savedHeapAtPre.sort());
            result.put(originalSavedHeapAtPre, savedHeapAtPre);
            }

        return result;
    }
    
    
    private Map<Term,Term> getInverseReplaceMap(
            Term selfTerm,
            Term heapAtPre,
            Term savedHeapAtPre,
            Services services) {
       final Map<Term,Term> result = new LinkedHashMap<Term,Term>();
       final Map<Term, Term> replaceMap = getReplaceMap(selfTerm, heapAtPre, savedHeapAtPre, services);
       for(Map.Entry<Term, Term> next: replaceMap.entrySet()) {
           result.put(next.getValue(), next.getKey());
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
            		     Term savedHeapAtPre,
            		     Services services) {
        assert (selfTerm == null) == (originalSelfTerm == null);
        Map<Term, Term> replaceMap = getReplaceMap(selfTerm, heapAtPre, savedHeapAtPre, services);
        OpReplacer or = new OpReplacer(replaceMap);
        return or.replace(savedHeapAtPre == null ? originalInvariant : originalTransactionInvariant);
    }
    
    
    @Override
    public Term getModifies(Term selfTerm,
            		    Term heapAtPre,
            		    Term savedHeapAtPre,
            		    Services services) {
        assert (selfTerm == null) == (originalSelfTerm == null);
        Map<Term, Term> replaceMap = 
            getReplaceMap(selfTerm, heapAtPre, savedHeapAtPre, services);
        OpReplacer or = new OpReplacer(replaceMap);
        return or.replace(savedHeapAtPre == null ? originalModifies : originalModifiesBackup);
    }
    

    @Override
    public Term getVariant(Term selfTerm, 
            		   Term heapAtPre,
            		   Services services) {
        assert (selfTerm == null) == (originalSelfTerm == null);
        Map<Term, Term> replaceMap = 
            getReplaceMap(selfTerm, heapAtPre, null, services);
        OpReplacer or = new OpReplacer(replaceMap);
        return or.replace(originalVariant);
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
    public Term getInternalSavedHeapAtPre() {
        return originalSavedHeapAtPre;
    }

    
    @Override
    public LoopInvariant setLoop(LoopStatement loop) {
        return new LoopInvariantImpl(loop,
                                     originalInvariant,
                                     originalTransactionInvariant,
                                     originalModifies,
                                     originalModifiesBackup,
                                     originalVariant,
                                     originalSelfTerm,
                                     originalHeapAtPre,
                                     originalSavedHeapAtPre);
    }
    
    
    @Override
    public LoopInvariant setInvariant(Term invariant, 
            			      Term selfTerm,
            			      Term heapAtPre,
            			      Term savedHeapAtPre,
            			      Services services) {
        assert (selfTerm == null) == (originalSelfTerm == null);
        Map inverseReplaceMap 
            = getInverseReplaceMap(selfTerm, heapAtPre, savedHeapAtPre, services);
        OpReplacer or = new OpReplacer(inverseReplaceMap);
        final boolean transaction = savedHeapAtPre != null;
        return new LoopInvariantImpl(loop, 
                                     transaction ? originalInvariant : or.replace(invariant), 
                                     transaction ? or.replace(invariant) :  originalTransactionInvariant,  
                                     originalModifies, 
                                     originalModifiesBackup, 
                                     originalVariant, 
                                     originalSelfTerm,
                                     originalHeapAtPre,
                                     originalSavedHeapAtPre);
    }
    
    
    @Override
    public void visit(Visitor v) {
        v.performActionOnLoopInvariant(this);
    }
    
    
    @Override
    public String toString() {
        return "invariant: " 
                + originalInvariant
                + "; invariant_transaction: "
                + originalTransactionInvariant
                + "; modifies: " 
                + originalModifies
                + "; modifies_backup: " 
                + originalModifiesBackup
                + "; variant: "
                + originalVariant;
    }


    @Override
    public String getDisplayName() {
	return "loop invariant";
    }


    @Override
    public KeYJavaType getKJT() {
	assert false;
	return null;
    }


    @Override
    public String getName() {
	return "loop invariant";
    }


    @Override
    public VisibilityModifier getVisibility() {
	assert false;
	return null;
    }
}

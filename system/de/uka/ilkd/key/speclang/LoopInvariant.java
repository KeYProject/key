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

import java.util.Map;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.logic.SetOfLocationDescriptor;
import de.uka.ilkd.key.logic.SetOfTerm;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Operator;


/**
 * A loop invariant, consisting of an invariant formula, a set of loop 
 * predicates, a modifier set, and a variant term.
 */
public interface LoopInvariant {
    
    /**
     * Returns the loop to which the invariant belongs.
     */
    public LoopStatement getLoop();

    /**
     * Returns the invariant formula.
     */
    public Term getInvariant(Term selfTerm, 
            Term memoryArea,
            /*inout*/ Map<Operator, Function/* (atPre)*/> atPreFunctions,
            Services services);
    
    /**
     * Returns the invariant formula.
     */
    public Term getInvariant(Term selfTerm, 
            /*inout*/ Map<Operator, Function/* (atPre)*/> atPreFunctions,
            Services services);
    
    /**
     * Returns the set of loop predicates.
     */
    public SetOfTerm getPredicates(Term selfTerm, 
            /*inout*/ Map <Operator, Function/* (atPre)*/> atPreFunctions,
            Services services);
    
    /**
     * Returns the modifier set.
     */
    public SetOfLocationDescriptor getModifies(
            Term selfTerm,
            Term memoryArea,
            /*inout*/ Map <Operator, Function/* (atPre)*/> atPreFunctions,
            Services services);
    /**
     * Returns the modifier set.
     */
    public SetOfLocationDescriptor getModifies(
            Term selfTerm,
            /*inout*/ Map <Operator, Function/* (atPre)*/> atPreFunctions,
            Services services);
    
    /**
     * Returns the variant term. 
     */
    public Term getVariant(Term selfTerm, 
            /*inout*/Map<Operator, Function/* (atPre)*/> atPreFunctions,
            Services services);
    
    /**
     * Returns the working space term (for the local scope). 
     */
    public Term getWorkingSpace(Term selfTerm, 
            /*inout*/Map<Operator, Function/* (atPre)*/> atPreFunctions,
            Services services);
    
    /**
     * Returns the working space term for the constructed scope. 
     */
    public Term getWorkingSpaceConstructed(Term selfTerm, 
            /*inout*/Map<Operator, Function/* (atPre)*/> atPreFunctions,
            Services services);
    
    /**
     * Returns the working space term for the reentrant scope. 
     */
    public Term getWorkingSpaceReentrant(Term selfTerm, 
            /*inout*/Map<Operator, Function/* (atPre)*/> atPreFunctions,
            Services services);
    
    /**
     * Tells whether using heuristics for generating additional loop predicates 
     * is allowed or not.
     */
    public boolean getPredicateHeuristicsAllowed();
    
    /**
     * Returns the term internally used for self. 
     * Use with care - it is likely that this is *not* the right "self" for you.
     */
    public Term getInternalSelfTerm();
    
    /**
     * Returns a copy of the internal map of atPre-functions.
     */
    public Map<Operator, Function> getInternalAtPreFunctions();
    
    /**
     * Returns a new loop invariant where the loop reference has been
     * replaced with the passed one.
     */
    public LoopInvariant setLoop(LoopStatement loop); 
    
    /**
     * Returns a new loop invariant where the invariant formula has been
     * repaced with the passed one. Take care: the variables used for
     * the receiver, parameters, and local variables must stay the same!
     */
    public LoopInvariant setInvariant(Term invariant, 
            Term selfTerm,
            /*inout*/ Map<Operator, Function/*atPre*/> atPreFunctions,
            Services services); 
    
    /**
     * Returns a new loop invariant where the loop predicates have been 
     * replaced with the passed ones.
     */
    public LoopInvariant setPredicates(SetOfTerm predicates, 
            Term selfTerm,
            /*inout*/ Map<Operator, Function/*atPre*/> atPreFunctions,
            Services services);
    
    /**
     * Returns a new loop invariant where the flag for predicate generation
     * heuristics has been set to the passed value. Take care: the variables 
     * used for the receiver, parameters, and local variables must stay the 
     * same!
     */
    public LoopInvariant setPredicateHeuristicsAllowed(
                                        boolean predicateHeuristicsAllowed);
    
    /** 
     * Loop invariants can be visited like source elements:
     * This method calls the corresponding method of a visitor in order to
     * perform some action/transformation on this element.
     */
    public void visit(Visitor v);
}

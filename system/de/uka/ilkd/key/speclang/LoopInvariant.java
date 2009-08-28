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


import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.logic.Term;


/**
 * A loop invariant, consisting of an invariant formula, a set of loop 
 * predicates, a modifies clause, and a variant term.
 */
public interface LoopInvariant extends SpecificationElement {
    
    /**
     * Returns the loop to which the invariant belongs.
     */
    public LoopStatement getLoop();

    /**
     * Returns the invariant formula.
     */
    public Term getInvariant(Term selfTerm, 
            		     Term heapAtPre,
            		     Services services);
    
    /**
     * Returns the set of loop predicates.
     */
    public ImmutableSet<Term> getPredicates(Term selfTerm, 
            			   	    Term heapAtPre,
            			   	    Services services);
    
    /**
     * Returns the modifies clause.
     */
    public Term getModifies(Term selfTerm, 
            		    Term heapAtPre,
            		    Services services);
    
    /**
     * Returns the variant term. 
     */
    public Term getVariant(Term selfTerm, 
            		   Term heapAtPre,
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
     * Returns the operator internally used for the pre-heap.
     */
    public Term getInternalHeapAtPre();
    
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
            			      Term heapAtPre,
            			      Services services); 
    
    /**
     * Returns a new loop invariant where the loop predicates have been 
     * replaced with the passed ones.
     */
    public LoopInvariant setPredicates(ImmutableSet<Term> predicates, 
            Term selfTerm,
            Term heapAtPre,
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

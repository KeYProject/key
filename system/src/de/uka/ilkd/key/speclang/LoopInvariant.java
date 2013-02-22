// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 


package de.uka.ilkd.key.speclang;

import java.util.Map;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.LocationVariable;


/**
 * A loop invariant, consisting of an invariant formula, a set of loop 
 * predicates, a modifies clause, and a variant term.
 */
public interface LoopInvariant extends SpecificationElement {
    
    /**
     * Returns the loop to which the invariant belongs.
     */
    public LoopStatement getLoop();

    
    /** Returns the invariant formula. */
    public Term getInvariant(LocationVariable heap, Term selfTerm, Map<LocationVariable,Term> atPres, Services services);

    /**
     * Returns the modifies clause.
     */
    public Term getModifies(LocationVariable heap, Term selfTerm, Map<LocationVariable,Term> atPres, Services services);
    
    /**
     * Returns the variant term. 
     */
    public Term getVariant(Term selfTerm, 
            		   Map<LocationVariable,Term> atPres,
            		   Services services);
    
    /**
     * Returns the term internally used for self. 
     * Use with care - it is likely that this is *not* the right "self" for you.
     */
    public Term getInternalSelfTerm();
    
    /**
     * Returns operators internally used for the pre-heap.
     */
    public Map<LocationVariable,Term> getInternalAtPres();

    /**
     * Returns the term internally used for the invariant. 
     * Use with care - it is likely that this is *not* the right "self" for you.
     */
    public Map<LocationVariable,Term> getInternalInvariants();

    /**
     * Returns the term internally used for the variant. 
     * Use with care - it is likely that this is *not* the right "self" for you.
     */
    public Term getInternalVariant();
    
    public Map<LocationVariable,Term> getInternalModifies();

    /**
     * Returns a new loop invariant where the loop reference has been
     * replaced with the passed one.
     */
    public LoopInvariant setLoop(LoopStatement loop); 
    
    /**
     * Returns a new loop invariant where the invariant formula has been
     * replaced with the passed one. Take care: the variables used for
     * the receiver, parameters, and local variables must stay the same!
     */
    public LoopInvariant setInvariant(Map<LocationVariable,Term> invariants, 
            			      Term selfTerm,
            			      Map<LocationVariable,Term> atPres,
            			      Services services); 
    
    /** 
     * Loop invariants can be visited like source elements:
     * This method calls the corresponding method of a visitor in order to
     * perform some action/transformation on this element.
     */
    public void visit(Visitor v);
    
    /**
     * Returns the invariant in pretty plain text format.
     */
    public String getPlainText(Services services);

}

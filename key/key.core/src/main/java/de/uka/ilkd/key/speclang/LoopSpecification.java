// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.speclang;

import java.util.Map;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.speclang.Contract.OriginalVariables;
import de.uka.ilkd.key.util.InfFlowSpec;



/**
 * A loop invariant, consisting of an invariant formula, a set of loop 
 * predicates, a modifies clause, and a variant term.
 */
public interface LoopSpecification extends SpecificationElement {

    /**
     * Returns the loop to which the invariant belongs.
     */
    public LoopStatement getLoop();

    /**
     * Returns the contracted function symbol.
     */
    public IProgramMethod getTarget();

    /**
     * Returns the invariant formula.
     * @param heap the heap variable.
     * @param selfTerm the self term.
     * @param atPres the operators used for the pre-heap.
     * @param services the Services object.
     * @return The invariant formula as a term.
     */
    public Term getInvariant(LocationVariable heap, Term selfTerm,
                             Map<LocationVariable, Term> atPres,
                             Services services);

    public Term getInvariant(Services services);

    /** Returns the free invariant formula. */
    public Term getFreeInvariant(LocationVariable heap, Term selfTerm,
    		Map<LocationVariable,Term> atPres, Services services);

    public Term getFreeInvariant(Services services);

    /**
     * Returns the modifies clause.
     * @param heap the heap variable.
     * @param selfTerm the self term.
     * @param atPres the operators used for the pre-heap.
     * @param services the Services object.
     * @return The modifies clause as a term.
     */
    public Term getModifies(LocationVariable heap, Term selfTerm,
                            Map<LocationVariable, Term> atPres,
                            Services services);

    /**
     * Returns the modifies clause.
     * @param selfTerm the self term.
     * @param atPres the operators used for the pre-heap.
     * @param services the Services object.
     * @return The modifies clause as a term.
     */
    public Term getModifies(Term selfTerm,
                            Map<LocationVariable, Term> atPres,
                            Services services);

    /**
     * Returns the information flow specification clause.
     */
    public ImmutableList<InfFlowSpec> getInfFlowSpecs(LocationVariable heap);

    public ImmutableList<InfFlowSpec> getInfFlowSpecs(Services services);

    public ImmutableList<InfFlowSpec> getInfFlowSpecs(LocationVariable heap,
                                                      Term selfTerm,
                                                      Map<LocationVariable, Term> atPres,
                                                      Services services);

    public boolean hasInfFlowSpec(Services services);

    /**
     * Returns the variant term.
     * @param selfTerm the self term.
     * @param atPres the operators used for the pre-heap.
     * @param services the Services object.
     * @return The variant term.
     */
    public Term getVariant(Term selfTerm,
                           Map<LocationVariable, Term> atPres,
                           Services services);

    /**
     * Returns the term internally used for self.
     * Use with care - it is likely that this is *not* the right "self" for you.
     */
    public Term getInternalSelfTerm();

    public Term getModifies();

    /**
     * Returns operators internally used for the pre-heap.
     * @return The map storing the operators.
     */
    public Map<LocationVariable, Term> getInternalAtPres();

    /**
     * Returns the term internally used for the invariant.
     * Use with care - it is likely that this is *not* the right "self" for you.
     * @return The map with an invariant for each heap location.
     */
    public Map<LocationVariable, Term> getInternalInvariants();

    /**
     * Returns the term internally used for the "free" invariant.
     * Use with care - it is likely that this is *not* the right "self" for you.
     * @return The map with a "free" invariant for each heap location.
     */
    public Map<LocationVariable, Term> getInternalFreeInvariants();

    /**
     * Returns the term internally used for the variant.
     * Use with care - it is likely that this is *not* the right "self" for you.
     * @return The variant clause as a term.
     */
    public Term getInternalVariant();

    /**
     * Returns the term internally used for the modifies clause.
     * Use with care - it is likely that this is *not* the right "self" for you.
     * @return The map with a modifies clause for each heap location.
     */
    public Map<LocationVariable, Term> getInternalModifies();

    public Map<LocationVariable,
               ImmutableList<InfFlowSpec>> getInternalInfFlowSpec();

    /**
     * Create and return a new loop specification element from the existing one
     * where the arguments given are replaced.
     * @param loop the new loop statement.
     * @param pm the new program method.
     * @param kjt the new KeYJavaType.
     * @param invariants the new loop invariant clauses.
     * @param freeInvariants the new "free" loop invariant clauses.
     * @param modifies the new modifies clauses.
     * @param infFlowSpecs the new information flow specification elements.
     * @param variant the new loop variant term.
     * @param selfTerm the new self term.
     * @param localIns the new local in-variables.
     * @param localOuts the new local out-variables.
     * @param atPres the new operators used for the pre-heap.
     * @return The new loop specification element.
     */
    public LoopSpecification create(LoopStatement loop,
                                    IProgramMethod pm,
                                    KeYJavaType kjt,
                                    Map<LocationVariable, Term> invariants,
                                    Map<LocationVariable, Term> freeInvariants,
                                    Map<LocationVariable, Term> modifies,
                                    Map<LocationVariable,
                                        ImmutableList<InfFlowSpec>> infFlowSpecs,
                                    Term variant,
                                    Term selfTerm,
                                    ImmutableList<Term> localIns,
                                    ImmutableList<Term> localOuts,
                                    Map<LocationVariable, Term> atPres);

    /**
     * Create and return a new loop specification element from the existing one
     * where the arguments given are replaced.
     * @param loop the new loop statement.
     * @param invariants the new loop invariant clauses.
     * @param freeInvariants the new "free" loop invariant clauses.
     * @param modifies the new modifies clauses.
     * @param infFlowSpecs the new information flow specification elements.
     * @param variant the new loop variant term.
     * @param selfTerm the new self term.
     * @param localIns the new local in-variables.
     * @param localOuts the new local out-variables.
     * @param atPres the new operators used for the pre-heap.
     * @return The new loop specification element.
     */
    public LoopSpecification create(LoopStatement loop,
                                    Map<LocationVariable, Term> invariants,
                                    Map<LocationVariable, Term> freeInvariants,
                                    Map<LocationVariable, Term> modifies,
                                    Map<LocationVariable,
                                        ImmutableList<InfFlowSpec>> infFlowSpecs,
                                    Term variant,
                                    Term selfTerm,
                                    ImmutableList<Term> localIns,
                                    ImmutableList<Term> localOuts,
                                    Map<LocationVariable, Term> atPres);

    /**
     * Instantiate a (raw) loop specification with loop invariant clauses and
     * a loop variant, possibly together with (if any) "free" loop invariant
     * clauses.
     * @param invariants the loop invariant clauses for instantiation.
     * @param freeInvariants the "free" loop invariant clauses for instantiation.
     * @param variant the loop variant for instantiation.
     * @return the instantiated loop specification.
     */
    public LoopSpecification instantiate(Map<LocationVariable, Term> invariants,
                                         Map<LocationVariable, Term> freeInvariants,
                                         Term variant);

    /**
     * Configure the existing loop specification element with new elements,
     * i.e., loop invariant clauses, a loop variant, modifies clauses,
     * information flow specification elements, and a loop variant,
     * possibly together with (if any) "free" loop invariant clauses.
     * @param invariants the new loop invariant clauses.
     * @param freeInvariants the new "free" loop invariant clauses.
     * @param modifies the new modifies clauses.
     * @param infFlowSpecs the new information flow specification elements.
     * @param variant the new loop variant.
     * @return The configured loop specification.
     */
    public LoopSpecification configurate(Map<LocationVariable, Term> invariants,
                                         Map<LocationVariable, Term> freeInvariants,
                                         Map<LocationVariable, Term> modifies,
                                         Map<LocationVariable,
                                                 ImmutableList<InfFlowSpec>> infFlowSpecs,
                                         Term variant);

    /**
     * Returns a new loop invariant where the loop reference has been
     * replaced with the passed one.
     */
    public LoopSpecification setLoop(LoopStatement loop);

    public LoopSpecification setTarget(IProgramMethod newPM);

    /**
     * Returns a new loop invariant where the invariant formula has been
     * replaced with the passed one. Take care: the variables used for
     * the receiver, parameters, and local variables must stay the same!
     * @param invariants the loop invariant clauses.
     * @param freeInvariants the "free" loop invariant clauses.
     * @param selfTerm the self term.
     * @param atPres the operators used for the pre-heap.
     * @param services the Services object.
     * @return The new loop invariant.
     */
    public LoopSpecification setInvariant(Map<LocationVariable, Term> invariants,
                                          Map<LocationVariable, Term> freeInvariants,
                                          Term selfTerm,
                                          Map<LocationVariable, Term> atPres,
                                          Services services);

    /** 
     * Loop invariants can be visited like source elements:
     * This method calls the corresponding method of a visitor in order to
     * perform some action/transformation on this element.
     */
    public void visit(Visitor v);
    
    /**
     * Returns the invariant in pretty plain text format.
     * @param services the Services object.
     * @param heapContext all corresponding heaps.
     * @param usePrettyPrinting whether the text should be pretty-printed.
     * @param useUnicodeSymbols whether Unicode symbols should be used.
     * @return a String containing the plain text representation of this
     *         invariant.
     */
    public String getPlainText(Services services,
                               Iterable<LocationVariable> heapContext,
                               boolean usePrettyPrinting,
                               boolean useUnicodeSymbols);

    public String getUniqueName();

    public KeYJavaType getKJT();

    public LoopSpecification setTarget(KeYJavaType newKJT, IObserverFunction newPM);

    /**
     * Returns the original Self Variable to replace it easier.
     */
    public OriginalVariables getOrigVars();

}
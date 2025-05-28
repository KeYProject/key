/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang;

import java.util.Map;
import java.util.function.UnaryOperator;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.speclang.Contract.OriginalVariables;
import de.uka.ilkd.key.util.InfFlowSpec;

import org.key_project.util.collection.ImmutableList;



/**
 * A loop invariant, consisting of an invariant formula, a set of loop predicates, a modifiable
 * clause, and a variant term.
 */
public interface LoopSpecification extends SpecificationElement {

    @Override
    LoopSpecification map(UnaryOperator<JTerm> op, Services services);

    /**
     * Returns the loop to which the invariant belongs.
     */
    LoopStatement getLoop();

    /**
     * Returns the contracted function symbol.
     */
    IProgramMethod getTarget();

    /**
     * Returns the invariant formula.
     *
     * @param heap the heap variable.
     * @param selfTerm the self term.
     * @param atPres the operators used for the pre-heap.
     * @param services the Services object.
     * @return The invariant formula as a term.
     */
    JTerm getInvariant(LocationVariable heap, JTerm selfTerm,
            Map<LocationVariable, JTerm> atPres, Services services);

    JTerm getInvariant(Services services);

    /** Returns the free invariant formula. */
    JTerm getFreeInvariant(LocationVariable heap, JTerm selfTerm,
            Map<LocationVariable, JTerm> atPres, Services services);

    JTerm getFreeInvariant(Services services);

    /**
     * Returns the modifiable clause.
     *
     * @param heap the heap variable.
     * @param selfTerm the self term.
     * @param atPres the operators used for the pre-heap.
     * @param services the Services object.
     * @return The modifiable clause as a term.
     */
    JTerm getModifiable(LocationVariable heap, JTerm selfTerm,
            Map<LocationVariable, JTerm> atPres, Services services);

    /**
     * Returns the modifiable clause.
     *
     * @param selfTerm the self term.
     * @param atPres the operators used for the pre-heap.
     * @param services the Services object.
     * @return The modifiable clause as a term.
     */
    JTerm getModifiable(JTerm selfTerm, Map<LocationVariable, JTerm> atPres, Services services);

    /**
     * Returns the free modifiable clause.
     *
     * @param heap the heap variable.
     * @param selfTerm the self term.
     * @param atPres the operators used for the pre-heap.
     * @param services the Services object.
     * @return The modifiable clause as a term.
     */
    JTerm getFreeModifiable(LocationVariable heap, JTerm selfTerm,
            Map<LocationVariable, JTerm> atPres,
            Services services);

    /**
     * Returns the information flow specification clause.
     */
    ImmutableList<InfFlowSpec> getInfFlowSpecs(LocationVariable heap);

    ImmutableList<InfFlowSpec> getInfFlowSpecs(Services services);

    ImmutableList<InfFlowSpec> getInfFlowSpecs(LocationVariable heap, JTerm selfTerm,
            Map<LocationVariable, JTerm> atPres, Services services);

    boolean hasInfFlowSpec(Services services);

    /**
     * Returns the variant term.
     *
     * @param selfTerm the self term.
     * @param atPres the operators used for the pre-heap.
     * @param services the Services object.
     * @return The variant term.
     */
    JTerm getVariant(JTerm selfTerm, Map<LocationVariable, JTerm> atPres, Services services);

    /**
     * Returns the term internally used for self. Use with care - it is likely that this is *not*
     * the right "self" for you.
     */
    JTerm getInternalSelfTerm();

    JTerm getModifiable();

    /**
     * Returns operators internally used for the pre-heap.
     *
     * @return The map storing the operators.
     */
    Map<LocationVariable, JTerm> getInternalAtPres();

    /**
     * Returns the term internally used for the invariant. Use with care - it is likely that this is
     * *not* the right "self" for you.
     *
     * @return The map with an invariant for each heap location.
     */
    Map<LocationVariable, JTerm> getInternalInvariants();

    /**
     * Returns the term internally used for the "free" invariant. Use with care - it is likely that
     * this is *not* the right "self" for you.
     *
     * @return The map with a "free" invariant for each heap location.
     */
    Map<LocationVariable, JTerm> getInternalFreeInvariants();

    /**
     * Returns the term internally used for the variant. Use with care - it is likely that this is
     * *not* the right "self" for you.
     *
     * @return The variant clause as a term.
     */
    JTerm getInternalVariant();

    /**
     * Returns the term internally used for the modifiable clause. Use with care - it is likely that
     * this is *not* the right "self" for you.
     *
     * @return The map with a modifiable clause for each heap location.
     */
    Map<LocationVariable, JTerm> getInternalModifiable();

    /**
     * Returns the term internally used for the modifiable clause.
     * Use with care - it is likely that this is *not* the right "self" for you.
     *
     * @return The map with a modifiable clause for each heap location.
     */
    Map<LocationVariable, JTerm> getInternalFreeModifiable();


    Map<LocationVariable, ImmutableList<InfFlowSpec>> getInternalInfFlowSpec();

    /**
     * Create and return a new loop specification element from the existing one where the arguments
     * given are replaced.
     *
     * @param loop the new loop statement.
     * @param pm the new program method.
     * @param kjt the new KeYJavaType.
     * @param invariants the new loop invariant clauses.
     * @param freeInvariants the new "free" loop invariant clauses.
     * @param modifiable the new modifiable clauses.
     * @param freeModifiable the new free modifiable clauses.
     * @param infFlowSpecs the new information flow specification elements.
     * @param variant the new loop variant term.
     * @param selfTerm the new self term.
     * @param localIns the new local in-variables.
     * @param localOuts the new local out-variables.
     * @param atPres the new operators used for the pre-heap.
     * @return The new loop specification element.
     */
    LoopSpecification create(LoopStatement loop, IProgramMethod pm, KeYJavaType kjt,
            Map<LocationVariable, JTerm> invariants, Map<LocationVariable, JTerm> freeInvariants,
            Map<LocationVariable, JTerm> modifiable, Map<LocationVariable, JTerm> freeModifiable,
            Map<LocationVariable, ImmutableList<InfFlowSpec>> infFlowSpecs, JTerm variant,
            JTerm selfTerm, ImmutableList<JTerm> localIns, ImmutableList<JTerm> localOuts,
            Map<LocationVariable, JTerm> atPres);

    /**
     * Create and return a new loop specification element from the existing one where the arguments
     * given are replaced.
     *
     * @param loop the new loop statement.
     * @param invariants the new loop invariant clauses.
     * @param freeInvariants the new "free" loop invariant clauses.
     * @param modifiable the new modifiable clauses.
     * @param freeModifiable the new free modifiable clauses.
     * @param infFlowSpecs the new information flow specification elements.
     * @param variant the new loop variant term.
     * @param selfTerm the new self term.
     * @param localIns the new local in-variables.
     * @param localOuts the new local out-variables.
     * @param atPres the new operators used for the pre-heap.
     * @return The new loop specification element.
     */
    LoopSpecification create(LoopStatement loop,
            Map<LocationVariable, JTerm> invariants, Map<LocationVariable, JTerm> freeInvariants,
            Map<LocationVariable, JTerm> modifiable, Map<LocationVariable, JTerm> freeModifiable,
            Map<LocationVariable, ImmutableList<InfFlowSpec>> infFlowSpecs, JTerm variant,
            JTerm selfTerm, ImmutableList<JTerm> localIns, ImmutableList<JTerm> localOuts,
            Map<LocationVariable, JTerm> atPres);

    /**
     * Instantiate a (raw) loop specification with loop invariant clauses and a loop variant,
     * possibly together with (if any) "free" loop invariant clauses.
     *
     * @param invariants the loop invariant clauses for instantiation.
     * @param freeInvariants the "free" loop invariant clauses for instantiation.
     * @param variant the loop variant for instantiation.
     * @return the instantiated loop specification.
     */
    LoopSpecification instantiate(Map<LocationVariable, JTerm> invariants,
            Map<LocationVariable, JTerm> freeInvariants, JTerm variant);

    /**
     * Configure the existing loop specification element with new elements, i.e., loop invariant
     * clauses, a loop variant, modifiable clauses, information flow specification elements, and a
     * loop variant, possibly together with (if any) "free" loop invariant clauses.
     *
     * @param invariants the new loop invariant clauses.
     * @param freeInvariants the new "free" loop invariant clauses.
     * @param modifiable the new modifiable clauses.
     * @param freeModifiable the new free modifiable clauses.
     * @param infFlowSpecs the new information flow specification elements.
     * @param variant the new loop variant.
     * @return The configured loop specification.
     */
    LoopSpecification configurate(
            Map<LocationVariable, JTerm> invariants, Map<LocationVariable, JTerm> freeInvariants,
            Map<LocationVariable, JTerm> modifiable, Map<LocationVariable, JTerm> freeModifiable,
            Map<LocationVariable, ImmutableList<InfFlowSpec>> infFlowSpecs, JTerm variant);

    /**
     * Returns a new loop invariant where the loop reference has been replaced with the passed one.
     */
    LoopSpecification setLoop(LoopStatement loop);

    LoopSpecification setTarget(IProgramMethod newPM);

    /**
     * Returns a new loop invariant where the invariant formula has been replaced with the passed
     * one. Take care: the variables used for the receiver, parameters, and local variables must
     * stay the same!
     *
     * @param invariants the loop invariant clauses.
     * @param freeInvariants the "free" loop invariant clauses.
     * @param selfTerm the self term.
     * @param atPres the operators used for the pre-heap.
     * @param services the Services object.
     * @return The new loop invariant.
     */
    LoopSpecification setInvariant(Map<LocationVariable, JTerm> invariants,
            Map<LocationVariable, JTerm> freeInvariants, JTerm selfTerm,
            Map<LocationVariable, JTerm> atPres, Services services);

    /**
     * Loop invariants can be visited like source elements: This method calls the corresponding
     * method of a visitor in order to perform some action/transformation on this element.
     */
    void visit(Visitor v);

    /**
     * Returns the invariant in pretty plain text format.
     *
     * @param services the Services object.
     * @param heapContext all corresponding heaps.
     * @param usePrettyPrinting whether the text should be pretty-printed.
     * @param useUnicodeSymbols whether Unicode symbols should be used.
     * @return a String containing the plain text representation of this invariant.
     */
    String getPlainText(Services services, Iterable<LocationVariable> heapContext,
            boolean usePrettyPrinting, boolean useUnicodeSymbols);

    String getUniqueName();

    @Override
    KeYJavaType getKJT();

    LoopSpecification setTarget(KeYJavaType newKJT, IObserverFunction newPM);

    /**
     * Returns the original Self Variable to replace it easier.
     */
    OriginalVariables getOrigVars();

}

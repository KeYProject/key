package de.uka.ilkd.key.loopinvgen;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.modifier.VisibilityModifier;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.JFunction;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.LoopSpecification;
import de.uka.ilkd.key.util.InfFlowSpec;
import org.jetbrains.annotations.Nullable;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import java.util.HashMap;
import java.util.Map;
import java.util.function.UnaryOperator;


/**
 * A loop invariant, consisting of an invariant formula, a set of loop
 * predicates, a modifies clause, and a variant term.
 */
public class LoopSpecificationImpl implements LoopSpecification {

    private final LoopStatement loop;
    private final Term loopInv;
    /**
     * The original invariant terms for each heap.
     */
    private final Map<LocationVariable, Term> originalInvariants;

    public LoopSpecificationImpl(LoopStatement loop, Term loopInv, LocationVariable heap) {
        this.loop = loop;
        this.loopInv = loopInv;
        originalInvariants = new HashMap<>();
        originalInvariants.put(heap, loopInv);
    }

    public LoopSpecificationImpl(LoopStatement loop, Term loopInv) {
        this.loop = loop;
        this.loopInv = loopInv;
        originalInvariants = null;
    }

    @Override
    public LoopSpecification map(UnaryOperator<Term> op, Services services) {
        return null;
    }

    @Override
    public LoopStatement getLoop() {
        return this.loop;
    }

    @Override
    public IProgramMethod getTarget() {//return exception
        return null;
    }

    @Override
    public Term getInvariant(LocationVariable heap, Term selfTerm, Map<LocationVariable, Term> atPres, Services services) {
        return loopInv;
    }

    @Override
    public Term getInvariant(Services services) {
        return this.loopInv;
    }

    @Override
    public Term getFreeInvariant(LocationVariable heap, Term selfTerm, Map<LocationVariable, Term> atPres, Services services) {
        return null;
    }

    @Override
    public Term getFreeInvariant(Services services) {
        return null;
    }

    @Override
    public Term getModifies(LocationVariable heap, Term selfTerm, Map<LocationVariable, Term> atPres, Services services) {
        Function func = services.getTypeConverter().getLocSetLDT().getAllLocs();
        return services.getTermBuilder().func(func);
    }

    @Override
    public Term getModifies(Term selfTerm, Map<LocationVariable, Term> atPres, Services services) {
        Function func = services.getTypeConverter().getLocSetLDT().getAllLocs();
        return services.getTermBuilder().func(func);
    }

    @Override
    public ImmutableList<InfFlowSpec> getInfFlowSpecs(LocationVariable heap) {
        return ImmutableSLList.<InfFlowSpec>nil();
    }

    @Override
    public ImmutableList<InfFlowSpec> getInfFlowSpecs(Services services) {
        return ImmutableSLList.<InfFlowSpec>nil();
    }

    @Override
    public ImmutableList<InfFlowSpec> getInfFlowSpecs(LocationVariable heap, Term selfTerm, Map<LocationVariable, Term> atPres, Services services) {
        return ImmutableSLList.<InfFlowSpec>nil();
    }

    @Override
    public boolean hasInfFlowSpec(Services services) {
        return false;
    }

    @Override
    public Term getVariant(Term selfTerm, Map<LocationVariable, Term> atPres, Services services) {
        return null;
    }

    @Override
    public Term getInternalSelfTerm() {
        return null;
    }

    @Override
    public Term getModifies() {
        return null;
    }

    @Override
    public Map<LocationVariable, Term> getInternalAtPres() {
        return new HashMap<>();
    }

    @Override
    public Map<LocationVariable, Term> getInternalInvariants() {
        return originalInvariants;
    }

    @Override
    public Map<LocationVariable, Term> getInternalFreeInvariants() {
        return new HashMap<>();
    }

    @Override
    public Term getInternalVariant() {
        return null;
    }

    @Override
    public Map<LocationVariable, Term> getInternalModifies() {
        return new HashMap<>();
    }

    @Override
    public Map<LocationVariable, ImmutableList<InfFlowSpec>> getInternalInfFlowSpec() {
        return new HashMap<>();
    }

    @Override
    public LoopSpecification create(LoopStatement loop, IProgramMethod pm, KeYJavaType kjt, Map<LocationVariable, Term> invariants, Map<LocationVariable, Term> freeInvariants, Map<LocationVariable, Term> modifies, Map<LocationVariable, ImmutableList<InfFlowSpec>> infFlowSpecs, Term variant, Term selfTerm, ImmutableList<Term> localIns, ImmutableList<Term> localOuts, Map<LocationVariable, Term> atPres) {
        return this;
    }

    @Override
    public LoopSpecification create(LoopStatement loop, Map<LocationVariable, Term> invariants, Map<LocationVariable, Term> freeInvariants, Map<LocationVariable, Term> modifies, Map<LocationVariable, ImmutableList<InfFlowSpec>> infFlowSpecs, Term variant, Term selfTerm, ImmutableList<Term> localIns, ImmutableList<Term> localOuts, Map<LocationVariable, Term> atPres) {
        return this;
    }

    @Override
    public LoopSpecification instantiate(Map<LocationVariable, Term> invariants, Map<LocationVariable, Term> freeInvariants, Term variant) {
        return this;
    }

    @Override
    public LoopSpecification configurate(Map<LocationVariable, Term> invariants, Map<LocationVariable, Term> freeInvariants, Map<LocationVariable, Term> modifies, Map<LocationVariable, ImmutableList<InfFlowSpec>> infFlowSpecs, Term variant) {
        return this;
    }

    @Override
    public LoopSpecification setLoop(LoopStatement loop) {
        return this;
    }

    @Override
    public LoopSpecification setTarget(IProgramMethod newPM) {
        return this;
    }

    @Override
    public LoopSpecification setInvariant(Map<LocationVariable, Term> invariants, Map<LocationVariable, Term> freeInvariants, Term selfTerm, Map<LocationVariable, Term> atPres, Services services) {
        return this;
    }

    @Override
    public void visit(Visitor v) {

    }

    @Override
    public String getPlainText(Services services, Iterable<LocationVariable> heapContext, boolean usePrettyPrinting, boolean useUnicodeSymbols) {
        return loopInv.toString();
    }

    @Override
    public String getUniqueName() {
        return null;
    }

    @Override
    public String getName() {
        return null;
    }

    @Override
    public String getDisplayName() {
        return null;
    }

    @Nullable
    @Override
    public VisibilityModifier getVisibility() {
        return null;
    }

    @Override
    public KeYJavaType getKJT() {
        return null;
    }

    @Override
    public LoopSpecification setTarget(KeYJavaType newKJT, IObserverFunction newPM) {
        return null;
    }

    @Override
    public Contract.OriginalVariables getOrigVars() {
        return null;
    }
}
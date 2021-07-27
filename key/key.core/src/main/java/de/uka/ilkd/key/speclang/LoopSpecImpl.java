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

import java.util.LinkedHashMap;
import java.util.Map;
import java.util.function.UnaryOperator;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.java.MapUtil;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.modifier.VisibilityModifier;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.speclang.Contract.OriginalVariables;
import de.uka.ilkd.key.util.InfFlowSpec;

/**
 * Standard implementation of the LoopInvariant interface.
 */
public final class LoopSpecImpl implements LoopSpecification {

    private final LoopStatement loop;
    private final IProgramMethod pm;
    private final KeYJavaType kjt;
    /**
     * The original invariant terms for each heap.
     */
    private final Map<LocationVariable, Term> originalInvariants;
    /**
     * The original free invariant terms for each heap.
     */
    private final Map<LocationVariable, Term> originalFreeInvariants;
    /**
     * The original modifies terms for each heap.
     */
    private final Map<LocationVariable, Term> originalModifies;
    /**
     * The original information flow specification element lists for each heap.
     */
    private final Map<LocationVariable, ImmutableList<InfFlowSpec>> originalInfFlowSpecs;
    private final Term originalVariant;
    private final Term originalSelfTerm;
    private final ImmutableList<Term> localIns;
    private final ImmutableList<Term> localOuts;
    /**
     * The mapping of the pre-heaps.
     */
    private final Map<LocationVariable, Term> originalAtPres;

    // -------------------------------------------------------------------------
    // constructors
    // -------------------------------------------------------------------------

    /**
     * Creates a loop invariant.
     *
     * @param loop the loop to which the invariant belongs.
     * @param pm the method containing the loop.
     * @param kjt the type of the class containing the method.
     * @param invariants the invariant formula for each heap.
     * @param freeInvariants the free invariant formula for each heap.
     * @param modifies the modifies clause for each heap.
     * @param infFlowSpecs low variables for information flow.
     * @param variant the variant term.
     * @param selfTerm the term used for the receiver object.
     * @param localIns the local variables read in the loop.
     * @param localOuts the local variables written in the loop.
     * @param atPres the term used for the at pre variables.
     */
    public LoopSpecImpl(LoopStatement loop,
            IProgramMethod pm,
            KeYJavaType kjt,
            Map<LocationVariable, Term> invariants,
            Map<LocationVariable, Term> freeInvariants,
            Map<LocationVariable, Term> modifies,
            Map<LocationVariable, ImmutableList<InfFlowSpec>> infFlowSpecs,
            Term variant,
            Term selfTerm,
            ImmutableList<Term> localIns,
            ImmutableList<Term> localOuts,
            Map<LocationVariable, Term> atPres) {
        assert loop != null;
        // assert modifies != null;
        // assert heapAtPre != null;
        this.loop = loop;
        this.pm = pm;
        this.kjt = kjt;
        this.originalInvariants = invariants == null ? new LinkedHashMap<LocationVariable, Term>()
                : invariants;
        this.originalFreeInvariants = freeInvariants == null
                ? new LinkedHashMap<LocationVariable, Term>()
                : freeInvariants;
        this.originalVariant = variant;
        this.originalModifies = modifies == null ? new LinkedHashMap<LocationVariable, Term>()
                : modifies;
        this.originalInfFlowSpecs = infFlowSpecs == null
                ? new LinkedHashMap<LocationVariable, ImmutableList<InfFlowSpec>>()
                : infFlowSpecs;
        this.originalSelfTerm = selfTerm;
        this.localIns = localIns;
        this.localOuts = localOuts;
        this.originalAtPres = atPres == null ? new LinkedHashMap<LocationVariable, Term>() : atPres;
    }

    /**
     * Creates an empty, default loop invariant for the passed loop.
     *
     * @param loop the loop to which the invariant belongs.
     * @param pm the method containing the loop.
     * @param kjt the type of the class containing the method.
     * @param selfTerm the term used for the receiver object.
     * @param atPres the term used for the at pre variables.
     */
    public LoopSpecImpl(LoopStatement loop,
            IProgramMethod pm,
            KeYJavaType kjt,
            Term selfTerm,
            Map<LocationVariable, Term> atPres) {
        this(loop, pm, kjt, null, null, null, null, null, selfTerm, null, null, atPres);
    }

    // -------------------------------------------------------------------------
    // internal methods
    // -------------------------------------------------------------------------

    private Map /* Operator, Operator, Term -> Term */<Term, Term> getReplaceMap(
            Term selfTerm,
            Map<LocationVariable, Term> atPres,
            Services services) {
        final Map<Term, Term> result = new LinkedHashMap<Term, Term>();

        // self
        if (selfTerm != null) {
//            assert selfTerm.sort().extendsTrans(originalSelfTerm.sort()) :
//        	   "instantiating sort " + originalSelfTerm.sort()
//        	   + " with sort " + selfTerm.sort()
//        	   + " which is not a subsort!";
            result.put(originalSelfTerm, selfTerm);
        }

        // -parameters and other local variables are always kept up to
        // date by the ProgVarReplaceVisitor

        if (atPres != null) {
            for (Map.Entry<LocationVariable, Term> en : originalAtPres.entrySet()) {
                LocationVariable var = en.getKey();
                Term replace = atPres.get(var);
                Term origReplace = en.getValue();
                if (replace != null && origReplace != null) {
                    assert replace.sort().equals(origReplace.sort());
                    result.put(origReplace, replace);
                }
            }
        }

        return result;
    }

    private Map<Term, Term> getInverseReplaceMap(Term selfTerm,
            Map<LocationVariable, Term> atPres,
            Services services) {
        final Map<Term, Term> result = new LinkedHashMap<Term, Term>();
        final Map<Term, Term> replaceMap = getReplaceMap(selfTerm, atPres, services);
        for (Map.Entry<Term, Term> next : replaceMap.entrySet()) {
            result.put(next.getValue(), next.getKey());
        }
        return result;
    }

    // -------------------------------------------------------------------------
    // public interface
    // -------------------------------------------------------------------------

    @Override
    public LoopSpecification map(UnaryOperator<Term> op, Services services) {
        Map<LocationVariable, Term> newInvariants = originalInvariants.entrySet().stream().collect(
                MapUtil.collector(Map.Entry::getKey, entry -> op.apply(entry.getValue())));
        Map<LocationVariable, Term> newFreeInvariants =
                originalFreeInvariants.entrySet().stream().collect(
                        MapUtil.collector(Map.Entry::getKey, entry -> op.apply(entry.getValue())));
        Map<LocationVariable, Term> newModifies = originalModifies.entrySet().stream().collect(
                MapUtil.collector(Map.Entry::getKey, entry -> op.apply(entry.getValue())));
        Map<LocationVariable, ImmutableList<InfFlowSpec>> newInfFlowSpecs =
                originalInfFlowSpecs.entrySet().stream().collect(MapUtil.collector(
                        Map.Entry::getKey,
                    entry -> entry.getValue().stream().map(spec -> spec.map(op))
                             .collect(ImmutableList.collector())));
        Term newVariant = op.apply(originalVariant);
        Term newSelfTerm = op.apply(originalSelfTerm);
        ImmutableList<Term> newLocalIns =
                localIns.stream().map(op).collect(ImmutableList.collector());
        ImmutableList<Term> newLocalOuts =
                localOuts.stream().map(op).collect(ImmutableList.collector());
        Map<LocationVariable, Term> newAtPres = originalAtPres.entrySet().stream().collect(
                MapUtil.collector(Map.Entry::getKey, entry -> op.apply(entry.getValue())));

        return new LoopSpecImpl(
                loop, pm, kjt,
                newInvariants, newFreeInvariants, newModifies,
                newInfFlowSpecs,
                newVariant, newSelfTerm,
                newLocalIns, newLocalOuts,
                newAtPres);
    }

    @Override
    public LoopStatement getLoop() {
        return loop;
    }

    @Override
    public Term getInvariant(LocationVariable heap,
            Term selfTerm,
            Map<LocationVariable, Term> atPres,
            Services services) {
        assert (selfTerm == null) == (originalSelfTerm == null);
        Map<Term, Term> replaceMap = getReplaceMap(selfTerm, atPres, services);
        OpReplacer or = new OpReplacer(replaceMap, services.getTermFactory(), services.getProof());
        return or.replace(originalInvariants.get(heap));
    }

    @Override
    public Term getInvariant(Services services) {
        return originalInvariants.get(services.getTypeConverter().getHeapLDT().getHeap());
    }

    @Override
    public Term getFreeInvariant(LocationVariable heap, Term selfTerm,
            Map<LocationVariable, Term> atPres,
            Services services) {
        assert (selfTerm == null) == (originalSelfTerm == null);
        Map<Term, Term> replaceMap = getReplaceMap(selfTerm, atPres, services);
        OpReplacer or = new OpReplacer(replaceMap, services.getTermFactory(), services.getProof());
        return or.replace(originalFreeInvariants.get(heap));
    }

    @Override
    public Term getFreeInvariant(Services services) {
        return originalFreeInvariants.get(services.getTypeConverter().getHeapLDT().getHeap());
    }

    @Override
    public Term getModifies(LocationVariable heap, Term selfTerm,
            Map<LocationVariable, Term> atPres,
            Services services) {
        assert (selfTerm == null) == (originalSelfTerm == null);
        Map<Term, Term> replaceMap = getReplaceMap(selfTerm, atPres, services);
        OpReplacer or = new OpReplacer(replaceMap, services.getTermFactory(), services.getProof());
        return or.replace(originalModifies.get(heap));
    }

    @Override
    public Term getModifies(Term selfTerm, Map<LocationVariable, Term> atPres, Services services) {
        assert (selfTerm == null) == (originalSelfTerm == null);
        LocationVariable baseHeap = services.getTypeConverter().getHeapLDT().getHeap();
        Map<Term, Term> replaceMap = getReplaceMap(selfTerm, atPres, services);
        OpReplacer or = new OpReplacer(replaceMap, services.getTermFactory(), services.getProof());
        return or.replace(originalModifies.get(baseHeap));
    }

    @Override
    public ImmutableList<InfFlowSpec> getInfFlowSpecs(LocationVariable heap,
            Term selfTerm,
            Map<LocationVariable, Term> atPres,
            Services services) {
        assert (selfTerm == null) == (originalSelfTerm == null);
        Map<Term, Term> replaceMap = getReplaceMap(selfTerm, atPres, services);
        OpReplacer or = new OpReplacer(replaceMap, services.getTermFactory(), services.getProof());
        return or.replaceInfFlowSpec(originalInfFlowSpecs.get(heap));
    }

    @Override
    public ImmutableList<InfFlowSpec> getInfFlowSpecs(LocationVariable heap) {
        return originalInfFlowSpecs.get(heap);
    }

    @Override
    public ImmutableList<InfFlowSpec> getInfFlowSpecs(Services services) {
        LocationVariable baseHeap = services.getTypeConverter().getHeapLDT().getHeap();
        return getInfFlowSpecs(baseHeap);
    }

    @Override
    public Term getVariant(Term selfTerm,
            Map<LocationVariable, Term> atPres,
            Services services) {
        assert (selfTerm == null) == (originalSelfTerm == null);
        Map<Term, Term> replaceMap = getReplaceMap(selfTerm, atPres, services);
        OpReplacer or = new OpReplacer(replaceMap, services.getTermFactory(), services.getProof());
        return or.replace(originalVariant);
    }

    @Override
    public Map<LocationVariable, Term> getInternalInvariants() {
        return originalInvariants;
    }

    @Override
    public Map<LocationVariable, Term> getInternalFreeInvariants() {
        return originalFreeInvariants;
    }

    @Override
    public Term getInternalVariant() {
        return originalVariant;
    }

    @Override
    public Map<LocationVariable, Term> getInternalModifies() {
        return originalModifies;
    }

    @Override
    public Map<LocationVariable, ImmutableList<InfFlowSpec>> getInternalInfFlowSpec() {
        return originalInfFlowSpecs;
    }

    @Override
    public Term getInternalSelfTerm() {
        return originalSelfTerm;
    }

    @Override
    public Term getModifies() {
        return originalModifies.values().iterator().next();
    }

    @Override
    public Map<LocationVariable, Term> getInternalAtPres() {
        Map<LocationVariable, Term> result = new LinkedHashMap<LocationVariable, Term>();
//        for(LocationVariable h : originalAtPres.keySet()) {
//          result.put(h, originalAtPres.get(h));
//        }
        result.putAll(originalAtPres);
        return result;
    }

    @Override
    public LoopSpecification create(LoopStatement loop,
            IProgramMethod pm,
            KeYJavaType kjt,
            Map<LocationVariable, Term> invariants,
            Map<LocationVariable, Term> freeInvariants,
            Map<LocationVariable, Term> modifies,
            Map<LocationVariable, ImmutableList<InfFlowSpec>> infFlowSpecs,
            Term variant,
            Term selfTerm,
            ImmutableList<Term> localIns,
            ImmutableList<Term> localOuts,
            Map<LocationVariable, Term> atPres) {
        return new LoopSpecImpl(loop, pm, kjt, invariants, freeInvariants,
                modifies, infFlowSpecs, variant, selfTerm,
                localIns, localOuts, atPres);
    }

    @Override
    public LoopSpecification create(LoopStatement loop,
            Map<LocationVariable, Term> invariants,
            Map<LocationVariable, Term> freeInvariants,
            Map<LocationVariable, Term> modifies,
            Map<LocationVariable, ImmutableList<InfFlowSpec>> infFlowSpecs,
            Term variant,
            Term selfTerm,
            ImmutableList<Term> localIns,
            ImmutableList<Term> localOuts,
            Map<LocationVariable, Term> atPres) {
        return create(loop, pm, kjt, invariants, freeInvariants, modifies, infFlowSpecs,
                variant, selfTerm, localIns, localOuts, atPres);
    }

    @Override
    public LoopSpecification instantiate(Map<LocationVariable, Term> invariants,
            Map<LocationVariable, Term> freeInvariants, Term variant) {
        return configurate(invariants, freeInvariants, originalModifies, originalInfFlowSpecs,
                variant);
    }

    @Override
    public LoopSpecification configurate(Map<LocationVariable, Term> invariants,
            Map<LocationVariable, Term> freeInvariants,
            Map<LocationVariable, Term> modifies,
            Map<LocationVariable, ImmutableList<InfFlowSpec>> infFlowSpecs,
            Term variant) {
        return create(loop, invariants, freeInvariants, modifies, infFlowSpecs, variant,
                originalSelfTerm, localIns, localOuts, originalAtPres);
    }

    @Override
    public LoopSpecification setLoop(LoopStatement loop) {
        return new LoopSpecImpl(loop,
                pm,
                kjt,
                originalInvariants,
                originalFreeInvariants,
                originalModifies,
                originalInfFlowSpecs,
                originalVariant,
                originalSelfTerm,
                localIns,
                localOuts,
                originalAtPres);
    }

    @Override
    public LoopSpecification setTarget(IProgramMethod newPM) {
        return new LoopSpecImpl(loop,
                newPM,
                kjt,
                originalInvariants,
                originalFreeInvariants,
                originalModifies,
                originalInfFlowSpecs,
                originalVariant,
                originalSelfTerm,
                localIns,
                localOuts,
                originalAtPres);
    }

    @Override
    public LoopSpecification setInvariant(Map<LocationVariable, Term> invariants,
            Map<LocationVariable, Term> freeInvariants,
            Term selfTerm,
            Map<LocationVariable, Term> atPres,
            Services services) {
        assert (selfTerm == null) == (originalSelfTerm == null);
        Map<Term, Term> inverseReplaceMap = getInverseReplaceMap(selfTerm, atPres, services);
        OpReplacer or = new OpReplacer(
                inverseReplaceMap, services.getTermFactory(), services.getProof());

        Map<LocationVariable, Term> newInvariants = new LinkedHashMap<LocationVariable, Term>();
        for (LocationVariable heap : invariants.keySet()) {
            newInvariants.put(heap, or.replace(invariants.get(heap)));
        }

        Map<LocationVariable, Term> newFreeInvariants = new LinkedHashMap<LocationVariable, Term>();
        for (LocationVariable heap : freeInvariants.keySet()) {
            newFreeInvariants.put(heap, or.replace(freeInvariants.get(heap)));
        }
        return new LoopSpecImpl(loop,
                pm,
                kjt,
                newInvariants,
                newFreeInvariants,
                originalModifies,
                originalInfFlowSpecs,
                originalVariant,
                originalSelfTerm,
                localIns,
                localOuts,
                originalAtPres);
    }

    @Override
    public void visit(Visitor v) {
        v.performActionOnLoopInvariant(this);
    }

    @Override
    public String toString() {
        return "invariants: "
                + originalInvariants
                + "free invariants: "
                + originalFreeInvariants
                + "; modifies: "
                + originalModifies
                + "; information flow specification: "
                + originalInfFlowSpecs
                + "; variant: "
                + originalVariant
                + "; input parameters: "
                + localIns
                + "; output parameters: "
                + localOuts;
    }

    /**
     * Return a plain text representation of this loop specification.
     * @param services the services object
     * @param usePrettyPrinting determines whether we get pretty or raw text
     * @param useUnicodeSymbols determines whether unicode will be used
     * @return the plain text representation as a string
     */
    public String getPlainText(Services services,
                               boolean usePrettyPrinting,
                               boolean useUnicodeSymbols) {
        final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
        return getPlainText(services, heapLDT.getAllHeaps(), usePrettyPrinting, useUnicodeSymbols);
    }

    @Override
    public String getPlainText(Services services, Iterable<LocationVariable> heapContext,
            boolean usePrettyPrinting, boolean useUnicodeSymbols) {
        final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
        final LocationVariable baseHeap = heapLDT.getHeap();

        String mods = "";
        for (LocationVariable h : heapContext) {
            if (originalModifies.get(h) != null) {
                String printMods = LogicPrinter.quickPrintTerm(originalModifies.get(h), services,
                        usePrettyPrinting, useUnicodeSymbols);
                mods = mods
                        + "\n"
                        + "mod"
                        + (h == baseHeap ? "" : "[" + h + "]")
                        + ": "
                        + printMods.trim();
            }
        }

        String invariants = "";
        for (LocationVariable h : heapContext) {
            if (originalInvariants.get(h) != null) {
                String printPosts = LogicPrinter.quickPrintTerm(originalInvariants.get(h), services,
                        usePrettyPrinting, useUnicodeSymbols);
                invariants = invariants
                        + "\n"
                        + "invariant"
                        + (h == baseHeap ? "" : "[" + h + "]")
                        + ": "
                        + printPosts.trim();
            }
        }

        return invariants
                + (originalVariant != null
                        ? ";\nvariant: " + LogicPrinter.quickPrintTerm(originalVariant, services,
                                usePrettyPrinting, useUnicodeSymbols).trim()
                        : ";")
                +
                mods;
    }

    @Override
    public String getDisplayName() {
        return "Loop Invariant";
    }

    @Override
    public IProgramMethod getTarget() {
        return this.pm;
    }

    @Override
    public KeYJavaType getKJT() {
        return this.kjt;
    }

    @Override
    public String getName() {
        return "Loop Invariant";
    }

    @Override
    public String getUniqueName() {
        if (pm != null) {
            return "Loop Invariant " + getLoop().getStartPosition().getLine() +
                    " " + getTarget().getUniqueName();
        } else {
            return "Loop Invariant " + getLoop().getStartPosition().getLine() +
                    " " + Math.abs(getLoop().hashCode());
        }
    }

    @Override
    public VisibilityModifier getVisibility() {
        assert false;
        return null;
    }

    @Override
    public boolean hasInfFlowSpec(Services services) {
        return !getInfFlowSpecs(services).isEmpty();
    }

    @Override
    public LoopSpecification setTarget(KeYJavaType newKJT, IObserverFunction newPM) {
        assert newPM instanceof IProgramMethod;
        return new LoopSpecImpl(loop, (IProgramMethod) newPM, newKJT,
                originalInvariants, originalFreeInvariants, originalModifies,
                originalInfFlowSpecs, originalVariant,
                originalSelfTerm, localIns, localOuts,
                originalAtPres);
    }

    @Override
    public OriginalVariables getOrigVars() {
        Map<LocationVariable, ProgramVariable> atPreVars =
                new LinkedHashMap<LocationVariable, ProgramVariable>();
        for (LocationVariable h : originalAtPres.keySet()) {
            atPreVars.put(h, (ProgramVariable) originalAtPres.get(h).op());
        }
        final ProgramVariable self;
        if (this.originalSelfTerm != null
                && this.originalSelfTerm.op() instanceof ProgramVariable) {
            self = (ProgramVariable) this.originalSelfTerm.op();
        } else if (this.originalSelfTerm != null) {
            self = new LocationVariable(
                    new ProgramElementName(originalSelfTerm.op().toString()), kjt);
        } else {
            self = null;
        }
        return new OriginalVariables(self, null, null, atPreVars,
                ImmutableSLList.<ProgramVariable>nil());
    }

}

/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.speclang;

import java.util.*;
import java.util.Map.Entry;
import java.util.function.UnaryOperator;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.Statement;
import de.uka.ilkd.key.java.ast.StatementBlock;
import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.ast.declaration.ModifierKind;
import de.uka.ilkd.key.java.ast.expression.BinaryAssignment;
import de.uka.ilkd.key.java.ast.expression.Expression;
import de.uka.ilkd.key.java.ast.reference.MethodReference;
import de.uka.ilkd.key.java.ast.statement.CatchAllStatement;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.pp.PosTableLayouter;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.proof.init.ContractPO;
import de.uka.ilkd.key.proof.init.FunctionalOperationContractPO;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProofOblInput;

import org.key_project.logic.Named;
import org.key_project.logic.SyntaxElement;
import org.key_project.logic.op.Operator;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.java.MapUtil;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

import static de.uka.ilkd.key.logic.equality.RenamingTermProperty.RENAMING_TERM_PROPERTY;
import static de.uka.ilkd.key.util.Assert.assertEqualSort;
import static de.uka.ilkd.key.util.Assert.assertSubSort;

/**
 * Standard implementation of the OperationContract interface.
 */
@NullMarked
public class FunctionalOperationContractImpl implements FunctionalOperationContract {

    final @Nullable String baseName;
    final String name;
    final KeYJavaType kjt;
    final IProgramMethod pm;
    final KeYJavaType specifiedIn;
    final JModality.JavaModalityKind modalityKind;
    /**
     * The original precondition terms.
     */
    final Map<LocationVariable, JTerm> originalPres;
    /**
     * The original free/unchecked precondition terms.
     */
    final Map<LocationVariable, JTerm> originalFreePres;
    final @Nullable JTerm originalMby;
    /**
     * The original postcondition terms.
     */
    final Map<LocationVariable, JTerm> originalPosts;
    /**
     * The original free/unchecked postcondition terms.
     */
    final Map<LocationVariable, JTerm> originalFreePosts;
    /**
     * The original axiom terms.
     */
    final @Nullable Map<LocationVariable, JTerm> originalAxioms;
    /**
     * The original modifiable clause terms.
     */
    final Map<LocationVariable, JTerm> originalModifiables;
    /**
     * The original modifiable_free clause terms.
     */
    final Map<LocationVariable, JTerm> originalFreeModifiables;
    final Map<LocationVariable, JTerm> originalDeps;
    final @Nullable LocationVariable originalSelfVar;
    final ImmutableList<LocationVariable> originalParamVars;
    final @Nullable LocationVariable originalResultVar;
    final @Nullable LocationVariable originalExcVar;
    /**
     * The mapping of the pre-heap variables.
     */
    final Map<LocationVariable, LocationVariable> originalAtPreVars;
    final @Nullable JTerm globalDefs;
    final int id;
    final boolean transaction;
    final boolean toBeSaved;

    /**
     * If a method is strictly pure, it has no modifiable clause which could be anonymised.
     *
     * @see #hasModifiable(LocationVariable)
     */
    final Map<LocationVariable, Boolean> hasRealModifiable;
    /**
     * @see #hasFreeModifiable(LocationVariable)
     */
    final Map<LocationVariable, Boolean> hasRealFreeModifiable;

    /**
     * The term builder.
     */
    private final TermBuilder tb;
    /**
     * The services object.
     */
    private final TermServices services;

    // -------------------------------------------------------------------------
    // constructors
    // -------------------------------------------------------------------------

    /**
     * Creates an operation contract. Using this constructor is discouraged: it may change in the
     * future. Please use the factory methods in {@link ContractFactory}.
     *
     * @param baseName base name of the contract (does not have to be unique)
     * @param name name of the contract (should be unique)
     * @param kjt the KeYJavaType of the method's Java class
     * @param pm the IProgramMethod to which the contract belongs
     * @param specifiedIn TODO
     * @param modalityKind the modality of the contract
     * @param pres the precondition of the contract
     * @param freePres the free/unchecked precondition of the contract
     * @param mby the measured_by clause of the contract
     * @param posts the postcondition of the contract
     * @param freePosts the free/unchecked postcondition of the contract
     * @param axioms the class axioms of the method
     * @param modifiables the modifiable clause of the contract
     * @param modifiables the free modifiable clause of the contract
     * @param accessibles the dependency clause of the contract
     * @param hasRealModifiable whether the contract has a modifiable set
     * @param hasRealFreeModifiable whether the contract has a free modifiable set
     * @param selfVar the variable used for the receiver object
     * @param paramVars the variables used for the operation parameters
     * @param resultVar the variables used for the operation result
     * @param excVar the variable used for the thrown exception
     * @param atPreVars the variable used for the pre-heap
     * @param globalDefs definitions for the whole contract
     * @param id id of the contract (should be unique or INVALID_ID)
     * @param toBeSaved TODO
     * @param transaction TODO
     * @param services TODO
     */
    FunctionalOperationContractImpl(@Nullable String baseName, @Nullable String name,
            KeYJavaType kjt,
            IProgramMethod pm, KeYJavaType specifiedIn, JModality.JavaModalityKind modalityKind,
            Map<LocationVariable, JTerm> pres, Map<LocationVariable, JTerm> freePres,
            @Nullable JTerm mby,
            Map<LocationVariable, JTerm> posts, Map<LocationVariable, JTerm> freePosts,
            @Nullable Map<LocationVariable, JTerm> axioms,
            Map<LocationVariable, JTerm> modifiables, Map<LocationVariable, JTerm> freeModifiables,
            Map<LocationVariable, JTerm> accessibles,
            Map<LocationVariable, Boolean> hasRealModifiable,
            Map<LocationVariable, Boolean> hasRealFreeModifiable,
            @Nullable LocationVariable selfVar, ImmutableList<LocationVariable> paramVars,
            @Nullable LocationVariable resultVar, @Nullable LocationVariable excVar,
            Map<LocationVariable, LocationVariable> atPreVars, @Nullable JTerm globalDefs, int id,
            boolean toBeSaved, boolean transaction, TermServices services) {
        assert !(name == null && baseName == null);
        assert kjt != null;
        assert pm != null;
        assert pres != null;
        assert posts != null;
        assert freePres != null;
        assert freePosts != null;
        assert modalityKind != null;
        assert (selfVar == null) == pm.isStatic();
        assert globalDefs == null || globalDefs.sort() == JavaDLTheory.UPDATE;
        assert paramVars != null;
        assert paramVars.size() >= pm.getParameterDeclarationCount();
        // may be more parameters in specifications (ghost parameters)
        if (resultVar == null) {
            assert (pm.isVoid() || pm.isConstructor()) : "resultVar == null for method " + pm;
        } else {
            assert (!pm.isVoid() && !pm.isConstructor())
                    : "non-null result variable for void method or constructor "
                        + pm
                        + " with return type " + pm.getReturnType();
        }
        assert pm.isModel() || excVar != null;
        assert !atPreVars.isEmpty();
        assert services != null;
        this.services = services;
        this.tb = services.getTermBuilder();
        this.baseName = baseName;
        this.name = name != null ? name
                : ContractFactory.generateContractName(
                    Objects.requireNonNull(baseName, "baseName must be set if name is null"), kjt,
                    pm, specifiedIn, id);
        this.pm = pm;
        this.kjt = kjt;
        this.specifiedIn = specifiedIn;
        this.modalityKind = modalityKind;
        this.originalPres = pres;
        this.originalFreePres = freePres;
        this.originalMby = mby;
        this.originalPosts = posts;
        this.originalFreePosts = freePosts;
        this.originalAxioms = axioms;
        this.originalModifiables = modifiables;
        this.originalFreeModifiables = freeModifiables;
        this.originalDeps = accessibles;
        this.hasRealModifiable = hasRealModifiable;
        this.hasRealFreeModifiable = hasRealFreeModifiable;
        this.originalSelfVar = selfVar;
        this.originalParamVars = paramVars;
        this.originalResultVar = resultVar;
        this.originalExcVar = excVar;
        this.originalAtPreVars = atPreVars;
        this.globalDefs = globalDefs;
        this.id = id;
        this.transaction = transaction;
        this.toBeSaved = toBeSaved;
    }

    @Override
    public FunctionalOperationContract map(UnaryOperator<JTerm> op, Services services) {
        Map<LocationVariable, JTerm> newPres = originalPres.entrySet().stream()
                .collect(MapUtil.collector(Map.Entry::getKey, entry -> op.apply(entry.getValue())));
        Map<LocationVariable, JTerm> newFreePres = originalFreePres.entrySet().stream()
                .collect(MapUtil.collector(Map.Entry::getKey, entry -> op.apply(entry.getValue())));
        JTerm newMby = originalMby == null ? null : op.apply(originalMby);
        Map<LocationVariable, JTerm> newPosts = originalPosts.entrySet().stream()
                .collect(MapUtil.collector(Map.Entry::getKey, entry -> op.apply(entry.getValue())));
        Map<LocationVariable, JTerm> newFreePosts = originalFreePosts.entrySet().stream()
                .collect(MapUtil.collector(Map.Entry::getKey, entry -> op.apply(entry.getValue())));
        Map<LocationVariable, JTerm> newAxioms = originalAxioms == null ? null
                : originalAxioms.entrySet().stream().collect(
                    MapUtil.collector(Map.Entry::getKey, entry -> op.apply(entry.getValue())));
        Map<LocationVariable, JTerm> newModifiables = originalModifiables.entrySet().stream()
                .collect(MapUtil.collector(Map.Entry::getKey, entry -> op.apply(entry.getValue())));
        Map<LocationVariable, JTerm> newFreeModifiables =
            originalFreeModifiables.entrySet().stream().collect(
                MapUtil.collector(Map.Entry::getKey, entry -> op.apply(entry.getValue())));
        Map<LocationVariable, JTerm> newAccessibles = originalDeps.entrySet().stream()
                .collect(MapUtil.collector(Map.Entry::getKey, entry -> op.apply(entry.getValue())));
        JTerm newGlobalDefs = globalDefs == null ? null : op.apply(globalDefs);

        return new FunctionalOperationContractImpl(baseName, name, kjt, pm, specifiedIn,
            modalityKind,
            newPres, newFreePres, newMby, newPosts, newFreePosts, newAxioms, newModifiables,
            newFreeModifiables,
            newAccessibles, hasRealModifiable, hasRealFreeModifiable, originalSelfVar,
            originalParamVars, originalResultVar, originalExcVar, originalAtPreVars, newGlobalDefs,
            id, toBeSaved, transaction, services);
    }

    // -------------------------------------------------------------------------
    // internal methods
    // -------------------------------------------------------------------------

    /**
     * Get the according replace map for the given variables.
     *
     * @param selfVar the self variable
     * @param paramVars the parameter variables
     * @param resultVar the result variable
     * @param excVar the exception variable
     * @param atPreVars a map of pre-heaps to their variables
     * @param services the services object
     * @return the replacement map
     */
    protected Map<LocationVariable, LocationVariable> getReplaceMap(
            @Nullable LocationVariable selfVar,
            @Nullable ImmutableList<LocationVariable> paramVars,
            @Nullable LocationVariable resultVar,
            @Nullable LocationVariable excVar,
            @Nullable Map<LocationVariable, LocationVariable> atPreVars,
            Services services) {
        final Map<LocationVariable, LocationVariable> result = new LinkedHashMap<>();

        // self
        if (selfVar != null) {
            final LocationVariable originalSelf =
                Objects.requireNonNull(originalSelfVar, "no original self variable");
            assertSubSort(selfVar, originalSelf);
            result.put(originalSelf, selfVar);
        }

        // parameters
        if (paramVars != null) {
            assert originalParamVars.size() == paramVars.size();
            final Iterator<LocationVariable> it1 = originalParamVars.iterator();
            final Iterator<LocationVariable> it2 = paramVars.iterator();
            while (it1.hasNext()) {
                LocationVariable originalParamVar = it1.next();
                LocationVariable paramVar = it2.next();
                // allow contravariant parameter types
                assertSubSort(originalParamVar, paramVar);
                result.put(originalParamVar, paramVar);
            }
        }

        // result
        if (resultVar != null) {
            // workaround to allow covariant return types (bug #1384)
            final LocationVariable originalResult =
                Objects.requireNonNull(originalResultVar, "no original result variable");
            assertSubSort(resultVar, originalResult);
            result.put(originalResult, resultVar);
        }

        // exception
        if (excVar != null) {
            final LocationVariable originalExc =
                Objects.requireNonNull(originalExcVar, "no original exception variable");
            assertEqualSort(originalExc, excVar);
            result.put(originalExc, excVar);
        }

        if (atPreVars != null) {
            final HeapLDT heapLDT = Objects.requireNonNull(
                services.getTypeConverter().getHeapLDT(), "heap LDT");
            for (LocationVariable h : heapLDT.getAllHeaps()) {
                if (atPreVars.get(h) != null) {
                    final LocationVariable originalAtPreVar = Objects.requireNonNull(
                        originalAtPreVars.get(h), "no original atPre variable for heap: " + h);
                    assertEqualSort(originalAtPreVar, atPreVars.get(h));
                    result.put(originalAtPreVar, atPreVars.get(h));
                }
            }
        }

        return result;
    }

    @Deprecated
    protected Map<JTerm, JTerm> getReplaceMap(LocationVariable heap, JTerm heapTerm,
            @Nullable JTerm selfTerm,
            @Nullable ImmutableList<JTerm> paramTerms, Services services) {
        return getReplaceMap(heap, heapTerm, selfTerm, paramTerms, null, null, null, services);
    }

    // The deprecated atPre argument may legitimately be null for contracts without an atPre clause
    // (see the @Nullable atPre-related getters of the interface); the term maps below store such
    // nulls as-is, which the replacement-map construction tolerates.
    @Deprecated
    @SuppressWarnings("nullness:argument.type.incompatible")
    protected Map<JTerm, JTerm> getReplaceMap(LocationVariable heap, JTerm heapTerm,
            @Nullable JTerm selfTerm,
            @Nullable ImmutableList<JTerm> paramTerms, @Nullable JTerm resultTerm,
            @Nullable JTerm excTerm, @Nullable JTerm atPre,
            Services services) {
        Map<LocationVariable, JTerm> heapTerms = new LinkedHashMap<>();
        heapTerms.put(heap, heapTerm);
        Map<LocationVariable, JTerm> atPres = new LinkedHashMap<>();
        heapTerms.put(heap, atPre);
        return getReplaceMap(heapTerms, selfTerm, paramTerms, resultTerm, excTerm, atPres,
            services);
    }

    /**
     * Get the according replace map for the given variable terms.
     *
     * @param heapTerms the heap terms
     * @param selfTerm the self term
     * @param paramTerms the parameter terms
     * @param resultTerm the result term
     * @param excTerm the exception variable term
     * @param atPres a map of pre-heaps to their variable terms
     * @param services the services object
     * @return the replacement map
     *         <p>
     *         The heap LDT is always registered in the {@link Services} of a fully initialized KeY
     *         environment (see {@link de.uka.ilkd.key.java.TypeConverter#getHeapLDT()}); the
     *         dereference
     *         is suppressed with a scoped key.
     */
    @SuppressWarnings("nullness:dereference.of.nullable")
    protected Map<JTerm, JTerm> getReplaceMap(Map<LocationVariable, JTerm> heapTerms,
            @Nullable JTerm selfTerm,
            @Nullable ImmutableList<JTerm> paramTerms, @Nullable JTerm resultTerm,
            @Nullable JTerm excTerm,
            @Nullable Map<LocationVariable, JTerm> atPres, Services services) {
        final Map<JTerm, JTerm> result = new LinkedHashMap<>();

        // heaps
        for (LocationVariable heap : heapTerms.keySet()) {
            final JTerm heapTerm = heapTerms.get(heap);
            assert heapTerm == null || heapTerm.sort()
                    .equals(services.getTypeConverter().getHeapLDT().targetSort());
            result.put(tb.var(heap), heapTerm);
        }

        // self
        if (selfTerm != null) {
            final LocationVariable originalSelf =
                Objects.requireNonNull(originalSelfVar, "no original self variable");
            assertSubSort(selfTerm, originalSelf);
            result.put(tb.var(originalSelf), selfTerm);
        }

        // parameters
        if (paramTerms != null) {
            assert originalParamVars.size() == paramTerms.size();
            final Iterator<LocationVariable> it1 = originalParamVars.iterator();
            final Iterator<JTerm> it2 = paramTerms.iterator();
            while (it1.hasNext()) {
                LocationVariable originalParamVar = it1.next();
                JTerm paramTerm = it2.next();
                // TODO: what does this mean?
                assert paramTerm.sort().extendsTrans(originalParamVar.sort());
                result.put(tb.var(originalParamVar), paramTerm);
            }
        }

        // result
        if (resultTerm != null) {
            final LocationVariable originalResult =
                Objects.requireNonNull(originalResultVar, "no original result variable");
            assertSubSort(resultTerm, originalResult);
            result.put(tb.var(originalResult), resultTerm);
        }

        // exception
        if (excTerm != null) {
            final LocationVariable originalExc =
                Objects.requireNonNull(originalExcVar, "no original exception variable");
            assertEqualSort(originalExc, excTerm);
            result.put(tb.var(originalExc), excTerm);
        }

        if (atPres != null) {
            final HeapLDT heapLDT = Objects.requireNonNull(
                services.getTypeConverter().getHeapLDT(), "heap LDT");
            for (LocationVariable h : heapLDT.getAllHeaps()) {
                final JTerm atPreTerm = atPres.get(h);
                if (atPreTerm != null) {
                    final LocationVariable originalAtPreVar = Objects.requireNonNull(
                        originalAtPreVars.get(h), "no original atPre variable for heap: " + h);
                    assertEqualSort(originalAtPreVar, atPreTerm);
                    result.put(tb.var(originalAtPreVar), atPreTerm);
                }
            }
        }
        return result;
    }

    /** Make sure ghost parameters appear in the list of parameter variables. */
    private ImmutableList<LocationVariable> addGhostParams(
            ImmutableList<LocationVariable> paramVars) {
        // make sure ghost parameters are present
        ImmutableList<LocationVariable> ghostParams = ImmutableList.nil();
        for (LocationVariable param : originalParamVars) {
            if (param.isGhost()) {
                ghostParams = ghostParams.append(param);
            }
        }
        paramVars = paramVars.append(ghostParams);
        return paramVars;
    }

    /** Make sure ghost parameters appear in the list of parameter variables. */
    private ImmutableList<JTerm> addGhostParamTerms(ImmutableList<JTerm> paramVars) {
        // make sure ghost parameters are present
        ImmutableList<JTerm> ghostParams = ImmutableList.nil();
        for (LocationVariable param : originalParamVars) {
            if (param.isGhost()) {
                ghostParams = ghostParams.append(tb.var(param));
            }
        }
        paramVars = paramVars.append(ghostParams);
        return paramVars;
    }

    // -------------------------------------------------------------------------
    // public interface
    // -------------------------------------------------------------------------

    @Override
    public String getName() {
        return name;
    }

    @Override
    public int id() {
        return id;
    }

    @Override
    public KeYJavaType getKJT() {
        return kjt;
    }

    @Override
    public IProgramMethod getTarget() {
        return pm;
    }

    @Override
    public boolean hasMby() {
        return originalMby != null;
    }

    @Override
    public @Nullable JTerm getPre(LocationVariable heap, @Nullable LocationVariable selfVar,
            ImmutableList<LocationVariable> paramVars,
            Map<LocationVariable, LocationVariable> atPreVars, Services services) {
        assert (selfVar == null) == (originalSelfVar == null);
        assert paramVars != null : "null parameters";
        assert services != null;

        paramVars = addGhostParams(paramVars);
        assert paramVars.size() == originalParamVars.size() : "number of parameters does not match";

        final Map<LocationVariable, LocationVariable> replaceMap =
            getReplaceMap(selfVar, paramVars, null, null, atPreVars, services);
        final OpReplacer or =
            new OpReplacer(replaceMap, services.getTermFactory(), services.getProof());
        return or.replace(originalPres.get(heap));
    }

    @Override
    public @Nullable JTerm getPre(List<LocationVariable> heapContext,
            @Nullable LocationVariable selfVar,
            ImmutableList<LocationVariable> paramVars,
            Map<LocationVariable, LocationVariable> atPreVars, Services services) {
        JTerm result = null;
        for (LocationVariable heap : heapContext) {
            final @Nullable JTerm p = getPre(heap, selfVar, paramVars, atPreVars, services);
            if (result == null) {
                result = p;
            } else {
                result = tb.and(result,
                    Objects.requireNonNull(p, "no precondition for heap: " + heap));
            }
        }
        return result;
    }

    @Override
    public @Nullable JTerm getPre(LocationVariable heap, JTerm heapTerm, @Nullable JTerm selfTerm,
            ImmutableList<JTerm> paramTerms, Map<LocationVariable, JTerm> atPres,
            Services services) {
        assert heapTerm != null;
        assert (selfTerm == null) == (originalSelfVar == null);
        assert paramTerms != null;
        paramTerms = addGhostParamTerms(paramTerms);
        assert paramTerms.size() == originalParamVars.size();
        assert services != null;

        final Map<LocationVariable, JTerm> heapTerms = new LinkedHashMap<>();
        heapTerms.put(heap, heapTerm);

        final Map<JTerm, JTerm> replaceMap =
            getReplaceMap(heapTerms, selfTerm, paramTerms, null, null, atPres, services);
        final OpReplacer or =
            new OpReplacer(replaceMap, services.getTermFactory(), services.getProof());
        return or.replace(originalPres.get(heap));
    }

    @Override
    public @Nullable JTerm getPre(List<LocationVariable> heapContext,
            Map<LocationVariable, JTerm> heapTerms,
            @Nullable JTerm selfTerm, ImmutableList<JTerm> paramTerms,
            Map<LocationVariable, JTerm> atPres,
            Services services) {
        JTerm result = null;
        for (LocationVariable heap : heapContext) {
            final @Nullable JTerm p = getPre(heap,
                Objects.requireNonNull(heapTerms.get(heap), "no heap term for heap: " + heap),
                selfTerm, paramTerms, atPres, services);
            if (p == null) {
                continue;
            }
            if (result == null) {
                result = p;
            } else {
                result = tb.and(result, p);
            }
        }
        return result;
    }

    @Override
    public @Nullable JTerm getFreePre(LocationVariable heap, @Nullable LocationVariable selfVar,
            ImmutableList<LocationVariable> paramVars,
            Map<LocationVariable, LocationVariable> atPreVars, Services services) {
        assert (selfVar == null) == (originalSelfVar == null);
        assert paramVars != null : "null parameters";
        assert services != null;

        paramVars = addGhostParams(paramVars);
        assert paramVars.size() == originalParamVars.size() : "number of parameters does not match";

        final Map<LocationVariable, LocationVariable> replaceMap =
            getReplaceMap(selfVar, paramVars, null, null, atPreVars, services);
        final OpReplacer or =
            new OpReplacer(replaceMap, services.getTermFactory(), services.getProof());
        return or.replace(originalFreePres.get(heap));
    }

    @Override
    public @Nullable JTerm getFreePre(List<LocationVariable> heapContext,
            @Nullable LocationVariable selfVar,
            ImmutableList<LocationVariable> paramVars,
            Map<LocationVariable, LocationVariable> atPreVars, Services services) {
        JTerm result = null;
        for (LocationVariable heap : heapContext) {
            final @Nullable JTerm p = getFreePre(heap, selfVar, paramVars, atPreVars, services);
            if (result == null) {
                result = p;
            } else if (p != null) {
                result = tb.and(result, p);
            }
        }
        return result;
    }

    @Override
    public @Nullable JTerm getFreePre(LocationVariable heap, JTerm heapTerm,
            @Nullable JTerm selfTerm,
            ImmutableList<JTerm> paramTerms, Map<LocationVariable, JTerm> atPres,
            Services services) {
        assert heapTerm != null;
        assert (selfTerm == null) == (originalSelfVar == null);
        assert paramTerms != null;
        paramTerms = addGhostParamTerms(paramTerms);
        assert paramTerms.size() == originalParamVars.size();
        assert services != null;

        final Map<LocationVariable, JTerm> heapTerms = new LinkedHashMap<>();
        heapTerms.put(heap, heapTerm);

        final Map<JTerm, JTerm> replaceMap =
            getReplaceMap(heapTerms, selfTerm, paramTerms, null, null, atPres, services);
        final OpReplacer or =
            new OpReplacer(replaceMap, services.getTermFactory(), services.getProof());
        return or.replace(originalFreePres.get(heap));
    }

    @Override
    public @Nullable JTerm getRequires(LocationVariable heap) {
        return originalPres.get(heap);
    }

    @Override
    public @Nullable JTerm getEnsures(LocationVariable heap) {
        return originalPosts.get(heap);
    }

    @Override
    public @Nullable JTerm getModifiable(LocationVariable heap) {
        return originalModifiables.get(heap);
    }

    @Override
    public @Nullable JTerm getAccessible(LocationVariable heap) {
        return originalDeps.get(heap);
    }

    @Override
    public @Nullable JTerm getMby(@Nullable LocationVariable selfVar,
            ImmutableList<LocationVariable> paramVars,
            Services services) {
        assert (selfVar == null) == (originalSelfVar == null);
        assert paramVars != null;
        paramVars = addGhostParams(paramVars);
        assert paramVars.size() == originalParamVars.size();
        assert services != null;
        final Map<LocationVariable, LocationVariable> replaceMap =
            getReplaceMap(selfVar, paramVars, null, null, null, services);
        final OpReplacer or =
            new OpReplacer(replaceMap, services.getTermFactory(), services.getProof());
        return or.replace(originalMby);
    }

    @Override
    public @Nullable JTerm getMby(Map<LocationVariable, JTerm> heapTerms, @Nullable JTerm selfTerm,
            ImmutableList<JTerm> paramTerms, Map<LocationVariable, JTerm> atPres,
            Services services) {
        assert heapTerms != null;
        assert (selfTerm == null) == (originalSelfVar == null);
        assert paramTerms != null;
        paramTerms = addGhostParamTerms(paramTerms);
        assert paramTerms.size() == originalParamVars.size();
        assert services != null;
        final Map<JTerm, JTerm> replaceMap =
            getReplaceMap(heapTerms, selfTerm, paramTerms, null, null, atPres, services);
        final OpReplacer or =
            new OpReplacer(replaceMap, services.getTermFactory(), services.getProof());
        return or.replace(originalMby);
    }

    @Override
    public String getPlainText(Services services) {
        return getText(false, services);
    }

    @Override
    public String getHTMLText(Services services) {
        return getText(true, services);
    }

    private String getText(boolean includeHtmlMarkup, Services services) {
        return getText(pm, originalResultVar, originalSelfVar, originalParamVars, originalExcVar,
            hasMby(), originalMby, originalModifiables, hasRealModifiable, globalDefs, originalPres,
            originalFreePres, originalPosts, originalFreePosts, originalAxioms, getModalityKind(),
            transactionApplicableContract(), includeHtmlMarkup, services,
            NotationInfo.DEFAULT_PRETTY_SYNTAX, NotationInfo.DEFAULT_UNICODE_ENABLED,
            NotationInfo.DEFAULT_HIDE_PACKAGE_PREFIX);
    }

    /**
     * Builds the plain or HTML text of the given functional contract.
     * <p>
     * The clause maps built below may legitimately hold {@code null} values: the contract getters
     * (e.g. {@code getPre}, {@code getPost}, {@code getFreePost}, {@code getModifiable},
     * {@code getRepresentsAxiom}) return {@code null} for heaps without the corresponding clause,
     * and {@code atPres} entries may be absent for the given {@code heapContext}. The downstream
     * text generation ({@link #getClauseText}, {@link #getModifiableText}) explicitly skips
     * {@code null} clauses, so the resulting entries are stored as-is.
     */
    @SuppressWarnings("nullness:argument.type.incompatible")
    public static String getText(FunctionalOperationContract contract,
            ImmutableList<JTerm> contractParams, @Nullable JTerm resultTerm,
            @Nullable JTerm contractSelf,
            JTerm excTerm,
            LocationVariable baseHeap, JTerm baseHeapTerm, List<LocationVariable> heapContext,
            Map<LocationVariable, JTerm> atPres, boolean includeHtmlMarkup, Services services,
            boolean usePrettyPrinting, boolean useUnicodeSymbols,
            boolean hidePackagePrefix) {
        Operator originalSelfVar = contractSelf != null ? contractSelf.op() : null;
        Operator originalResultVar = resultTerm != null ? resultTerm.op() : null;
        final TermBuilder tb = services.getTermBuilder();

        Map<LocationVariable, JTerm> heapTerms = new LinkedHashMap<>();
        for (LocationVariable h : heapContext) {
            heapTerms.put(h, tb.var(h));
        }

        JTerm originalMby = contract.hasMby()
                ? contract.getMby(heapTerms, contractSelf, contractParams, atPres, services)
                : null;

        Map<LocationVariable, JTerm> originalModifiables = new HashMap<>();
        for (LocationVariable heap : heapContext) {
            JTerm m =
                contract.getModifiable(heap, tb.var(heap), contractSelf, contractParams, services);
            originalModifiables.put(heap, m);
        }

        Map<LocationVariable, Boolean> hasRealModifiable =
            new HashMap<>();
        for (LocationVariable heap : heapContext) {
            hasRealModifiable.put(heap, contract.hasModifiable(heap));
        }

        JTerm globalDefs =
            contract.getGlobalDefs(baseHeap, baseHeapTerm, contractSelf, contractParams, services);

        Map<LocationVariable, JTerm> originalPres = new HashMap<>();
        for (LocationVariable heap : heapContext) {
            JTerm preTerm = contract.getPre(heap,
                Objects.requireNonNull(heapTerms.get(heap), "no heap term for heap: " + heap),
                contractSelf, contractParams, atPres, services);
            originalPres.put(heap, preTerm);
        }

        Map<LocationVariable, JTerm> originalFreePres = new HashMap<>();
        for (LocationVariable heap : heapContext) {
            JTerm freePreTerm = contract.getFreePre(heap, Objects.requireNonNull(
                heapTerms.get(heap), "no heap term for heap: " + heap), contractSelf,
                contractParams, atPres, services);
            originalFreePres.put(heap, freePreTerm);
        }

        Map<LocationVariable, JTerm> originalPosts = new HashMap<>();
        for (LocationVariable heap : heapContext) {
            JTerm p = contract.getPost(heap,
                Objects.requireNonNull(heapTerms.get(heap), "no heap term for heap: " + heap),
                contractSelf, contractParams, resultTerm, excTerm, atPres, services);
            originalPosts.put(heap, p);
        }

        Map<LocationVariable, JTerm> originalFreePosts = new HashMap<>();
        for (LocationVariable heap : heapContext) {
            JTerm p = contract.getFreePost(heap, Objects.requireNonNull(heapTerms.get(heap),
                "no heap term for heap: " + heap), contractSelf, contractParams, resultTerm,
                excTerm, atPres, services);
            originalFreePosts.put(heap, p);
        }

        // TODO: Why is this never read?
        Map<LocationVariable, LocationVariable> atPresVars =
            new HashMap<>();
        for (Entry<LocationVariable, JTerm> entry : atPres.entrySet()) {
            if (entry.getValue() != null) {
                atPresVars.put(entry.getKey(), (LocationVariable) entry.getValue().op());
            } else {
                atPresVars.put(entry.getKey(), null);
            }
        }

        Map<LocationVariable, JTerm> originalAxioms = new HashMap<>();
        for (LocationVariable heap : heapContext) {
            JTerm p = contract.getRepresentsAxiom(heap, Objects.requireNonNull(
                heapTerms.get(heap), "no heap term for heap: " + heap), contractSelf,
                contractParams, resultTerm, excTerm, atPres, services);
            originalAxioms.put(heap, p);
        }

        return getText(contract.getTarget(), originalResultVar, originalSelfVar, contractParams,
            (LocationVariable) excTerm.op(), contract.hasMby(), originalMby, originalModifiables,
            hasRealModifiable, globalDefs, originalPres, originalFreePres, originalPosts,
            originalFreePosts, originalAxioms, contract.getModalityKind(),
            contract.transactionApplicableContract(), includeHtmlMarkup, services,
            usePrettyPrinting, useUnicodeSymbols, hidePackagePrefix);
    }


    private static String getSignatureText(IProgramMethod pm, @Nullable Operator originalResultVar,
            @Nullable Operator originalSelfVar,
            ImmutableList<? extends SyntaxElement> originalParamVars,
            @Nullable LocationVariable originalExcVar, Services services, boolean usePrettyPrinting,
            boolean useUnicodeSymbols, boolean hidePackagePrefix) {
        final StringBuilder sig = new StringBuilder();
        if (originalResultVar != null) {
            sig.append(originalResultVar);
            sig.append(" = ");
        } else if (pm.isConstructor()) {
            sig.append(originalSelfVar);
            sig.append(" = new ");
        }
        if (!pm.isStatic() && !pm.isConstructor()) {
            sig.append(originalSelfVar);
            sig.append(".");
        }
        sig.append(pm.getName());
        sig.append("(");
        for (SyntaxElement subst : originalParamVars) {
            if (subst instanceof Named named) {
                sig.append(named.name()).append(", ");
            } else if (subst instanceof JTerm) {
                sig.append(LogicPrinter.quickPrintTerm((JTerm) subst, services, usePrettyPrinting,
                    useUnicodeSymbols, hidePackagePrefix)).append(", ");
            } else {
                sig.append(subst).append(", ");
            }
        }
        if (!originalParamVars.isEmpty()) {
            sig.setLength(sig.length() - 2);
        }
        sig.append(")");
        if (!pm.isModel()) {
            sig.append(" catch(");
            sig.append(originalExcVar);
            sig.append(")");
        }
        return sig.toString();
    }


    private static String printClauseText(final String text, boolean includeHtmlMarkup,
            Services services, String clause, LocationVariable h,
            final JTerm clauseTerm, boolean usePrettyPrinting, boolean useUnicodeSymbols,
            boolean hidePackagePrefix) {
        final HeapLDT heapLDT = Objects.requireNonNull(services.getTypeConverter().getHeapLDT(),
            "heap LDT");
        final LocationVariable baseHeap = heapLDT.getHeap();

        String printClause =
            LogicPrinter.quickPrintTerm(clauseTerm, services, usePrettyPrinting, useUnicodeSymbols,
                hidePackagePrefix);
        clause = clause + (includeHtmlMarkup ? "<br><b>" : "\n") + text
                + (h == baseHeap ? "" : "[" + h + "]") + (includeHtmlMarkup ? "</b> " : ": ")
                + (includeHtmlMarkup ? LogicPrinter.escapeHTML(printClause, false)
                        : printClause);
        return clause;
    }

    private static String getClauseText(final String text,
            Map<LocationVariable, JTerm> originalClause, boolean includeHtmlMarkup,
            Services services, boolean usePrettyPrinting, boolean useUnicodeSymbols,
            boolean hidePackagePrefix) {
        String clause = "";
        final TermBuilder tb = services.getTermBuilder();
        final HeapLDT heapLDT = Objects.requireNonNull(services.getTypeConverter().getHeapLDT(),
            "heap LDT");

        for (LocationVariable h : heapLDT.getAllHeaps()) {
            JTerm clauseTerm = originalClause.get(h);
            if (clauseTerm != null && !clauseTerm.equals(tb.tt())) {
                clauseTerm = includeHtmlMarkup ? tb.unlabelRecursive(clauseTerm) : clauseTerm;
                clause = printClauseText(text, includeHtmlMarkup, services, clause, h, clauseTerm,
                    usePrettyPrinting,
                    useUnicodeSymbols, hidePackagePrefix);
            }
        }
        return clause;
    }

    private static String getGlobalUpdatesText(@Nullable JTerm globalDefs,
            boolean includeHtmlMarkup,
            Services services, boolean usePrettyPrinting, boolean useUnicodeSymbols,
            boolean hidePackagePrefix) {
        String globalUpdates = "";
        final TermBuilder tb = services.getTermBuilder();
        if (globalDefs != null) {
            globalDefs = includeHtmlMarkup ? tb.unlabelRecursive(globalDefs) : globalDefs;
            final String printUpdates = LogicPrinter.quickPrintTerm(globalDefs, services,
                usePrettyPrinting, useUnicodeSymbols, hidePackagePrefix);
            globalUpdates = (includeHtmlMarkup ? "<br><b>" : "\n") + "defs"
                + (includeHtmlMarkup ? "</b> " : ": ")
                + (includeHtmlMarkup ? LogicPrinter.escapeHTML(printUpdates, false)
                        : printUpdates.trim());
        }
        return globalUpdates;
    }

    private static String getModifiableText(Map<LocationVariable, JTerm> originalModifiables,
            Map<LocationVariable, Boolean> hasRealModifiable, boolean includeHtmlMarkup,
            Services services, boolean usePrettyPrinting, boolean useUnicodeSymbols,
            boolean hidePackagePrefix) {
        String modifiables = "";
        final HeapLDT heapLDT = Objects.requireNonNull(services.getTypeConverter().getHeapLDT(),
            "heap LDT");

        for (LocationVariable h : heapLDT.getAllHeaps()) {
            final JTerm modifiableTerm = originalModifiables.get(h);
            if (modifiableTerm != null) {
                modifiables =
                    printClauseText("modifiable", includeHtmlMarkup, services, modifiables, h,
                        modifiableTerm, usePrettyPrinting,
                        useUnicodeSymbols, hidePackagePrefix);
                if (!Objects.requireNonNull(hasRealModifiable.get(h),
                    "no modifiable flag for heap: " + h)) {
                    modifiables =
                        modifiables + (includeHtmlMarkup ? "<b>" : "") + ", creates no new objects"
                            + (includeHtmlMarkup ? "</b>" : "");
                }
            }
        }
        return modifiables;
    }

    private static String getPostText(Map<LocationVariable, JTerm> originalPosts,
            @Nullable Map<LocationVariable, JTerm> originalAxioms, boolean includeHtmlMarkup,
            Services services, boolean usePrettyPrinting, boolean useUnicodeSymbols,
            boolean hidePackagePrefix) {
        String posts = getClauseText("post", originalPosts, includeHtmlMarkup, services,
            usePrettyPrinting, useUnicodeSymbols, hidePackagePrefix);
        if (originalAxioms != null) {
            posts = posts + getClauseText("axiom", originalAxioms, includeHtmlMarkup, services,
                usePrettyPrinting, useUnicodeSymbols, hidePackagePrefix);
        }
        return posts;
    }

    private static String getText(IProgramMethod pm, @Nullable Operator originalResultVar,
            @Nullable Operator originalSelfVar,
            ImmutableList<? extends SyntaxElement> originalParamVars,
            @Nullable LocationVariable originalExcVar, boolean hasMby,
            @Nullable JTerm originalMby,
            Map<LocationVariable, JTerm> originalModifiables,
            Map<LocationVariable, Boolean> hasRealModifiable, @Nullable JTerm globalDefs,
            Map<LocationVariable, JTerm> originalPres,
            Map<LocationVariable, JTerm> originalFreePres,
            Map<LocationVariable, JTerm> originalPosts,
            Map<LocationVariable, JTerm> originalFreePosts,
            @Nullable Map<LocationVariable, JTerm> originalAxioms,
            JModality.JavaModalityKind modalityKind,
            boolean transaction,
            boolean includeHtmlMarkup, Services services, boolean usePrettyPrinting,
            boolean useUnicodeSymbols, boolean hidePackagePrefix) {
        final String sig = getSignatureText(pm, originalResultVar, originalSelfVar,
            originalParamVars, originalExcVar, services, usePrettyPrinting, useUnicodeSymbols,
            hidePackagePrefix);

        final String mby = hasMby
                ? LogicPrinter.quickPrintTerm(Objects.requireNonNull(originalMby,
                    "mby must be set when hasMby()"), services,
                    usePrettyPrinting, useUnicodeSymbols, hidePackagePrefix)
                : null;

        final String modifiables =
            getModifiableText(originalModifiables, hasRealModifiable, includeHtmlMarkup,
                services, usePrettyPrinting, useUnicodeSymbols, hidePackagePrefix);

        final String globalUpdates = getGlobalUpdatesText(globalDefs, includeHtmlMarkup, services,
            usePrettyPrinting, useUnicodeSymbols, hidePackagePrefix);

        final String pres = getClauseText("pre", originalPres, includeHtmlMarkup, services,
            usePrettyPrinting, useUnicodeSymbols, hidePackagePrefix);

        final String freePres = getClauseText("free pre", originalFreePres, includeHtmlMarkup,
            services, usePrettyPrinting, useUnicodeSymbols, hidePackagePrefix);

        final String freePosts = getClauseText("free post", originalFreePosts, includeHtmlMarkup,
            services, usePrettyPrinting, useUnicodeSymbols, hidePackagePrefix);

        final String posts = getPostText(originalPosts, originalAxioms, includeHtmlMarkup, services,
            usePrettyPrinting, useUnicodeSymbols, hidePackagePrefix);

        final String clauses = globalUpdates + pres + freePres + posts + freePosts + modifiables;
        if (includeHtmlMarkup) {
            return "<html>" + "<i>" + LogicPrinter.escapeHTML(sig, false) + "</i>" + clauses
                + (hasMby ? "<br><b>measured-by</b> "
                    + LogicPrinter.escapeHTML(
                        Objects.requireNonNull(mby, "mby string must be set when hasMby()"), false)
                        : "")
                + "<br><b>termination</b> " + modalityKind.name()
                + (transaction ? "<br><b>transaction applicable</b>" : "") + "</html>";

        } else {
            return sig + clauses + (hasMby ? "\nmeasured-by: " + mby : "") + "\ntermination: "
                + modalityKind + (transaction ? "\ntransaction applicable:" : "");
        }
    }

    @Override
    public boolean toBeSaved() {
        return toBeSaved;
    }

    @Override
    public String proofToString(Services services) {
        assert toBeSaved;
        final StringBuilder sb = new StringBuilder();
        final HeapLDT heapLDT = Objects.requireNonNull(services.getTypeConverter().getHeapLDT(),
            "heap LDT");
        final LocationVariable baseHeap = heapLDT.getHeap();
        sb.append(baseName).append(" {\n");

        // print var decls
        sb.append("  \\programVariables {\n");
        if (originalSelfVar != null) {
            sb.append("    ").append(originalSelfVar.proofToString());
        }
        for (LocationVariable originalParamVar : originalParamVars) {
            sb.append("    ").append(originalParamVar.proofToString());
        }
        if (originalResultVar != null) {
            sb.append("    ").append(originalResultVar.proofToString());
        }
        sb.append("    ")
                .append(Objects.requireNonNull(originalExcVar, "no original exception variable")
                        .proofToString());
        sb.append("    ").append(Objects
                .requireNonNull(originalAtPreVars.get(baseHeap),
                    "no original atPre variable for heap: " + baseHeap)
                .proofToString());
        sb.append("  }\n");

        // prepare Java program
        final Expression[] args = new LocationVariable[originalParamVars.size()];
        int i = 0;
        for (LocationVariable arg : originalParamVars) {
            args[i++] = arg;
        }
        final MethodReference mr = new MethodReference(new ImmutableArray<>(args),
            pm.getProgramElementName(), originalSelfVar);
        final Statement callStatement;
        if (originalResultVar == null) {
            callStatement = mr;
        } else {
            callStatement =
                new BinaryAssignment(BinaryAssignment.BinaryAssignmentKind.COPY, originalResultVar,
                    mr);
        }
        final CatchAllStatement cas = new CatchAllStatement(new StatementBlock(callStatement),
            originalExcVar);
        final StatementBlock sblock = new StatementBlock(cas);
        final JavaBlock jb = JavaBlock.createJavaBlock(sblock);

        // print contract term
        final JTerm update = tb.tf().createTerm(
            ElementaryUpdate.getInstance(Objects.requireNonNull(originalAtPreVars.get(baseHeap),
                "no original atPre variable for heap: " + baseHeap)),
            tb.getBaseHeap());
        final JTerm modalityTerm = tb.prog(modalityKind, jb, Objects.requireNonNull(
            originalPosts.get(baseHeap), "no postcondition for heap: " + baseHeap));
        final JTerm updateTerm =
            tb.tf().createTerm(UpdateApplication.UPDATE_APPLICATION, update, modalityTerm);
        final JTerm contractTerm = tb.tf().createTerm(Junctor.IMP, Objects.requireNonNull(
            originalPres.get(baseHeap), "no precondition for heap: " + baseHeap), updateTerm);
        final LogicPrinter lp =
            new LogicPrinter(new NotationInfo(), null, PosTableLayouter.pure());
        lp.printTerm(contractTerm);
        sb.append(lp.result());

        // print modifiable
        lp.reset();
        lp.printTerm(Objects.requireNonNull(originalModifiables.get(baseHeap),
            "no modifiable clause for heap: " + baseHeap));
        sb.append("  \\modifiable ").append(lp.result());

        sb.append("};\n");
        return sb.toString();
    }

    @Override
    public JModality.JavaModalityKind getModalityKind() {
        return modalityKind;
    }

    @Override
    public @Nullable JTerm getPost(LocationVariable heap, @Nullable LocationVariable selfVar,
            ImmutableList<LocationVariable> paramVars, @Nullable LocationVariable resultVar,
            @Nullable LocationVariable excVar, Map<LocationVariable, LocationVariable> atPreVars,
            Services services) {
        assert (selfVar == null) == (originalSelfVar == null);
        assert paramVars != null;
        paramVars = addGhostParams(paramVars);
        assert paramVars.size() == originalParamVars.size();
        assert (resultVar == null) == (originalResultVar == null);
        assert pm.isModel() || excVar != null;
        assert !atPreVars.isEmpty();
        assert services != null;
        final Map<LocationVariable, LocationVariable> replaceMap =
            getReplaceMap(selfVar, paramVars, resultVar, excVar, atPreVars, services);
        final OpReplacer or =
            new OpReplacer(replaceMap, services.getTermFactory(), services.getProof());
        return or.replace(originalPosts.get(heap));
    }

    @Override
    public @Nullable JTerm getPost(List<LocationVariable> heapContext,
            @Nullable LocationVariable selfVar,
            ImmutableList<LocationVariable> paramVars, @Nullable LocationVariable resultVar,
            @Nullable LocationVariable excVar, Map<LocationVariable, LocationVariable> atPreVars,
            Services services) {
        JTerm result = null;
        for (LocationVariable heap : heapContext) {
            final @Nullable JTerm p =
                getPost(heap, selfVar, paramVars, resultVar, excVar, atPreVars, services);
            if (result == null) {
                result = p;
            } else {
                result = tb.and(result,
                    Objects.requireNonNull(p, "no postcondition for heap: " + heap));
            }
        }
        return result;

    }

    @Override
    public @Nullable JTerm getPost(LocationVariable heap, JTerm heapTerm, @Nullable JTerm selfTerm,
            ImmutableList<JTerm> paramTerms, @Nullable JTerm resultTerm, @Nullable JTerm excTerm,
            Map<LocationVariable, JTerm> atPres, Services services) {
        assert heapTerm != null;
        assert (selfTerm == null) == (originalSelfVar == null);
        assert paramTerms != null;
        paramTerms = addGhostParamTerms(paramTerms);
        assert paramTerms.size() == originalParamVars.size();
        assert (resultTerm == null) == (originalResultVar == null);
        assert pm.isModel() || excTerm != null;
        assert !atPres.isEmpty();
        assert services != null;
        final Map<LocationVariable, JTerm> heapTerms = new LinkedHashMap<>();
        heapTerms.put(heap, heapTerm);

        final Map<JTerm, JTerm> replaceMap =
            getReplaceMap(heapTerms, selfTerm, paramTerms, resultTerm, excTerm, atPres, services);
        final OpReplacer or =
            new OpReplacer(replaceMap, services.getTermFactory(), services.getProof());
        return or.replace(originalPosts.get(heap));
    }

    @Override
    public @Nullable JTerm getPost(List<LocationVariable> heapContext,
            Map<LocationVariable, JTerm> heapTerms,
            @Nullable JTerm selfTerm, ImmutableList<JTerm> paramTerms, @Nullable JTerm resultTerm,
            @Nullable JTerm excTerm,
            Map<LocationVariable, JTerm> atPres, Services services) {
        JTerm result = null;
        for (LocationVariable heap : heapContext) {
            final @Nullable JTerm p = getPost(heap,
                Objects.requireNonNull(heapTerms.get(heap), "no heap term for heap: " + heap),
                selfTerm, paramTerms, resultTerm, excTerm, atPres, services);
            if (p == null) {
                continue;
            }
            if (result == null) {
                result = p;
            } else {
                result = tb.and(result, p);
            }
        }
        return result;
    }

    @Override
    public @Nullable JTerm getFreePost(LocationVariable heap, @Nullable LocationVariable selfVar,
            ImmutableList<LocationVariable> paramVars, @Nullable LocationVariable resultVar,
            @Nullable LocationVariable excVar, Map<LocationVariable, LocationVariable> atPreVars,
            Services services) {
        assert (selfVar == null) == (originalSelfVar == null);
        assert paramVars != null;
        paramVars = addGhostParams(paramVars);
        assert paramVars.size() == originalParamVars.size();
        assert (resultVar == null) == (originalResultVar == null);
        assert pm.isModel() || excVar != null;
        assert !atPreVars.isEmpty();
        assert services != null;
        final Map<LocationVariable, LocationVariable> replaceMap =
            getReplaceMap(selfVar, paramVars, resultVar, excVar, atPreVars, services);
        final OpReplacer or =
            new OpReplacer(replaceMap, services.getTermFactory(), services.getProof());
        return or.replace(originalFreePosts.get(heap));
    }

    @Override
    public @Nullable JTerm getFreePost(LocationVariable heap, JTerm heapTerm,
            @Nullable JTerm selfTerm,
            ImmutableList<JTerm> paramTerms, @Nullable JTerm resultTerm, @Nullable JTerm excTerm,
            Map<LocationVariable, JTerm> atPres, Services services) {
        assert heapTerm != null;
        assert (selfTerm == null) == (originalSelfVar == null);
        assert paramTerms != null;
        paramTerms = addGhostParamTerms(paramTerms);
        assert paramTerms.size() == originalParamVars.size();
        assert (resultTerm == null) == (originalResultVar == null);
        assert pm.isModel() || excTerm != null;
        assert atPres.size() != 0;
        assert services != null;
        final Map<LocationVariable, JTerm> heapTerms = new LinkedHashMap<>();
        heapTerms.put(heap, heapTerm);

        final Map<JTerm, JTerm> replaceMap =
            getReplaceMap(heapTerms, selfTerm, paramTerms, resultTerm, excTerm, atPres, services);
        final OpReplacer or =
            new OpReplacer(replaceMap, services.getTermFactory(), services.getProof());
        return or.replace(originalFreePosts.get(heap));
    }

    @Override
    public @Nullable JTerm getFreePost(List<LocationVariable> heapContext,
            Map<LocationVariable, JTerm> heapTerms, @Nullable JTerm selfTerm,
            ImmutableList<JTerm> paramTerms,
            @Nullable JTerm resultTerm, @Nullable JTerm excTerm,
            Map<LocationVariable, JTerm> atPres,
            Services services) {
        JTerm result = null;
        for (LocationVariable heap : heapContext) {
            final @Nullable JTerm p = getFreePost(heap, Objects.requireNonNull(heapTerms.get(heap),
                "no heap term for heap: " + heap), selfTerm, paramTerms, resultTerm, excTerm,
                atPres, services);
            if (p == null) {
                continue;
            }
            if (result == null) {
                result = p;
            } else {
                result = tb.and(result, p);
            }
        }
        return result;
    }

    @Override
    public @Nullable JTerm getFreePost(List<LocationVariable> heapContext,
            @Nullable LocationVariable selfVar,
            ImmutableList<LocationVariable> paramVars, @Nullable LocationVariable resultVar,
            @Nullable LocationVariable excVar, Map<LocationVariable, LocationVariable> atPreVars,
            Services services) {
        JTerm result = null;
        for (LocationVariable heap : heapContext) {
            final @Nullable JTerm p =
                getFreePost(heap, selfVar, paramVars, resultVar, excVar, atPreVars, services);
            if (result == null) {
                result = p;
            } else {
                result = tb.and(result,
                    Objects.requireNonNull(p, "no free postcondition for heap: " + heap));
            }
        }
        return result;

    }

    @Override
    public @Nullable JTerm getRepresentsAxiom(LocationVariable heap,
            @Nullable LocationVariable selfVar,
            ImmutableList<LocationVariable> paramVars, @Nullable LocationVariable resultVar,
            Map<LocationVariable, LocationVariable> atPreVars, Services services) {
        assert (selfVar == null) == (originalSelfVar == null) : "Illegal instantiation:"
            + (originalSelfVar == null
                    ? "this is a static contract, instantiated with self variable '" + selfVar + "'"
                    : "this is an instance contract, instantiated without a self variable");
        assert paramVars != null;
        assert paramVars.size() == originalParamVars.size();
        assert (resultVar == null) == (originalResultVar == null);
        assert !atPreVars.isEmpty();
        assert services != null;
        if (originalAxioms == null) {
            return null;
        }
        final Map<LocationVariable, LocationVariable> replaceMap =
            getReplaceMap(selfVar, paramVars, resultVar, null, atPreVars, services);
        final OpReplacer or =
            new OpReplacer(replaceMap, services.getTermFactory(), services.getProof());
        return or.replace(originalAxioms.get(heap));
    }

    @Override
    public @Nullable JTerm getRepresentsAxiom(LocationVariable heap, JTerm heapTerm,
            @Nullable JTerm selfTerm,
            ImmutableList<JTerm> paramTerms, @Nullable JTerm resultTerm, @Nullable JTerm excTerm,
            Map<LocationVariable, JTerm> atPres, Services services) {
        assert heapTerm != null;
        assert (selfTerm == null) == (originalSelfVar == null);
        assert paramTerms != null;
        paramTerms = addGhostParamTerms(paramTerms);
        assert paramTerms.size() == originalParamVars.size();
        assert (resultTerm == null) == (originalResultVar == null);
        assert pm.isModel() || excTerm != null;
        assert atPres.size() != 0;
        assert services != null;
        final Map<LocationVariable, JTerm> heapTerms = new LinkedHashMap<>();
        heapTerms.put(heap, heapTerm);

        final Map<JTerm, JTerm> replaceMap =
            getReplaceMap(heapTerms, selfTerm, paramTerms, resultTerm, excTerm, atPres, services);
        final OpReplacer or =
            new OpReplacer(replaceMap, services.getTermFactory(), services.getProof());
        final Map<LocationVariable, JTerm> axioms =
            Objects.requireNonNull(originalAxioms, "no axioms for contract");
        return or.replace(axioms.get(heap));
    }

    @Override
    public boolean isReadOnlyContract(Services services) {
        final HeapLDT heapLDT =
            Objects.requireNonNull(services.getTypeConverter().getHeapLDT(), "heap LDT");
        final JTerm baseModifiable = Objects.requireNonNull(
            originalModifiables.get(heapLDT.getHeap()),
            "no modifiable clause for heap: " + heapLDT.getHeap());
        return baseModifiable.op() == services.getTypeConverter().getLocSetLDT().getEmpty();
    }

    public @Nullable JTerm getAnyModifiable(@Nullable JTerm modifiable,
            @Nullable LocationVariable selfVar,
            ImmutableList<LocationVariable> paramVars, Services services) {
        assert (selfVar == null) == (originalSelfVar == null);
        assert paramVars != null;
        paramVars = addGhostParams(paramVars);
        assert paramVars.size() == originalParamVars.size();
        assert services != null;
        final Map<LocationVariable, LocationVariable> replaceMap =
            getReplaceMap(selfVar, paramVars, null, null, null, services);
        final OpReplacer or =
            new OpReplacer(replaceMap, services.getTermFactory(), services.getProof());
        return or.replace(modifiable);
    }

    @Override
    public @Nullable JTerm getModifiable(LocationVariable heap, @Nullable LocationVariable selfVar,
            ImmutableList<LocationVariable> paramVars, Services services) {
        return getAnyModifiable(this.originalModifiables.get(heap), selfVar, paramVars,
            services);
    }

    @Override
    public @Nullable JTerm getFreeModifiable(LocationVariable heap,
            @Nullable LocationVariable selfVar,
            ImmutableList<LocationVariable> paramVars, Services services) {
        return getAnyModifiable(this.originalFreeModifiables.get(heap), selfVar, paramVars,
            services);
    }

    private @Nullable JTerm getAnyModifiable(LocationVariable heap, @Nullable JTerm modifiable,
            JTerm heapTerm, @Nullable JTerm selfTerm,
            ImmutableList<JTerm> paramTerms, Services services) {
        assert heapTerm != null;
        assert (selfTerm == null) == (originalSelfVar == null);
        assert paramTerms != null;
        paramTerms = addGhostParamTerms(paramTerms);
        assert paramTerms.size() == originalParamVars.size();
        assert services != null;

        final Map<LocationVariable, JTerm> heapTerms = new LinkedHashMap<>();
        heapTerms.put(heap, heapTerm);

        final Map<JTerm, JTerm> replaceMap =
            getReplaceMap(heapTerms, selfTerm, paramTerms, null, null, null, services);
        final OpReplacer or =
            new OpReplacer(replaceMap, services.getTermFactory(), services.getProof());
        return or.replace(modifiable);
    }

    @Override
    public boolean hasModifiable(LocationVariable heap) {
        Boolean result = this.hasRealModifiable.get(heap);
        if (result == null) {
            return false;
        }
        return result;
    }

    @Override
    public boolean hasFreeModifiable(LocationVariable heap) {
        Boolean result = this.hasRealFreeModifiable.get(heap);
        if (result == null) {
            return false;
        }
        return result;
    }

    @Override
    public @Nullable JTerm getModifiable(LocationVariable heap, JTerm heapTerm,
            @Nullable JTerm selfTerm,
            ImmutableList<JTerm> paramTerms, Services services) {
        return getAnyModifiable(heap, this.originalModifiables.get(heap), heapTerm, selfTerm,
            paramTerms, services);
    }

    @Override
    public @Nullable JTerm getFreeModifiable(LocationVariable heap, JTerm heapTerm,
            @Nullable JTerm selfTerm, ImmutableList<JTerm> paramTerms, Services services) {
        return getAnyModifiable(heap, this.originalFreeModifiables.get(heap), heapTerm, selfTerm,
            paramTerms, services);
    }

    /**
     * The lookup for an {@code atPre} variable may legitimately miss for heaps that have no
     * pre-heap (cf. {@link ContractFactory}, where a missing atPre variable marks a non-pre
     * heap); the dependency term then falls through to {@code null} via
     * {@link OpReplacer#replace(de.uka.ilkd.key.logic.JTerm)}, which {@code getDep}'s
     * {@code @Nullable} contract allows.
     */
    @SuppressWarnings("nullness:argument.type.incompatible")
    @Override
    public @Nullable JTerm getDep(LocationVariable heap, boolean atPre,
            @Nullable LocationVariable selfVar,
            ImmutableList<LocationVariable> paramVars,
            @Nullable Map<LocationVariable, LocationVariable> atPreVars, Services services) {
        assert (selfVar == null) == (originalSelfVar == null);
        assert paramVars != null;
        assert paramVars.size() == originalParamVars.size();
        assert services != null;
        Map<SyntaxElement, SyntaxElement> map = new LinkedHashMap<>();
        if (originalSelfVar != null) {
            // the assertion (selfVar == null) == (originalSelfVar == null) above guarantees a
            // non-null selfVar here
            map.put(originalSelfVar,
                Objects.requireNonNull(selfVar, "no self variable"));
        }
        for (LocationVariable originalParamVar : originalParamVars) {
            map.put(originalParamVar, paramVars.head());
            paramVars = paramVars.tail();
        }
        if (atPreVars != null && originalAtPreVars != null) {
            final HeapLDT heapLDT = Objects.requireNonNull(
                services.getTypeConverter().getHeapLDT(), "heap LDT");
            for (LocationVariable h : heapLDT.getAllHeaps()) {
                LocationVariable originalAtPreVar = originalAtPreVars.get(h);
                final LocationVariable atPreVar = atPreVars.get(h);
                if (atPreVar != null && originalAtPreVar != null) {
                    map.put(tb.var(atPre ? h : originalAtPreVar), tb.var(atPreVar));
                }
            }
        }
        OpReplacer or = new OpReplacer(map, services.getTermFactory(), services.getProof());
        return or.replace(originalDeps.get(atPre ? originalAtPreVars.get(heap) : heap));
    }

    /**
     * The lookup for an {@code atPre} variable may legitimately miss for heaps that have no
     * pre-heap (cf. {@link ContractFactory}, where a missing atPre variable marks a non-pre
     * heap); the dependency term then falls through to {@code null} via
     * {@link OpReplacer#replace(de.uka.ilkd.key.logic.JTerm)}, which {@code getDep}'s
     * {@code @Nullable} contract allows.
     */
    @SuppressWarnings("nullness:argument.type.incompatible")
    @Override
    public @Nullable JTerm getDep(LocationVariable heap, boolean atPre, JTerm heapTerm,
            @Nullable JTerm selfTerm,
            ImmutableList<JTerm> paramTerms, @Nullable Map<LocationVariable, JTerm> atPres,
            Services services) {
        assert heapTerm != null;
        assert (selfTerm == null) == (originalSelfVar == null);
        assert paramTerms != null;
        assert paramTerms.size() == originalParamVars.size();
        assert services != null;
        Map<SyntaxElement, SyntaxElement> map = new LinkedHashMap<>();
        map.put(tb.var(heap), heapTerm);
        if (originalSelfVar != null) {
            // the assertion (selfTerm == null) == (originalSelfVar == null) above guarantees a
            // non-null selfTerm here
            map.put(tb.var(originalSelfVar),
                Objects.requireNonNull(selfTerm, "no self term"));
        }
        for (LocationVariable originalParamVar : originalParamVars) {
            map.put(tb.var(originalParamVar), paramTerms.head());
            paramTerms = paramTerms.tail();
        }
        if (atPres != null && originalAtPreVars != null) {
            final HeapLDT heapLDT = Objects.requireNonNull(
                services.getTypeConverter().getHeapLDT(), "heap LDT");
            for (LocationVariable h : heapLDT.getAllHeaps()) {
                LocationVariable originalAtPreVar = originalAtPreVars.get(h);
                final JTerm atPreTerm = atPres.get(h);
                if (originalAtPreVar != null && atPreTerm != null) {
                    map.put(tb.var(originalAtPreVar), atPreTerm);
                }
            }
        }
        OpReplacer or = new OpReplacer(map, services.getTermFactory(), services.getProof());
        return or.replace(originalDeps.get(atPre ? originalAtPreVars.get(heap) : heap));
    }

    @Override
    public @Nullable JTerm getGlobalDefs() {
        return this.globalDefs;
    }

    @Override
    public @Nullable JTerm getGlobalDefs(LocationVariable heap, JTerm heapTerm,
            @Nullable JTerm selfTerm,
            ImmutableList<JTerm> paramTerms, Services services) {
        if (globalDefs == null) {
            return null;
        }
        assert heapTerm != null;
        assert (selfTerm == null) == (originalSelfVar == null);
        assert paramTerms != null;
        paramTerms = addGhostParamTerms(paramTerms);
        assert paramTerms.size() == originalParamVars.size();
        assert services != null;
        final Map<JTerm, JTerm> replaceMap =
            getReplaceMap(heap, heapTerm, selfTerm, paramTerms, services);
        final OpReplacer or =
            new OpReplacer(replaceMap, services.getTermFactory(), services.getProof());
        return or.replace(globalDefs);
    }

    @Override
    public String toString() {
        final LocationVariable heap = Objects.requireNonNull(
            ((Services) services).getTypeConverter().getHeapLDT(), "heap LDT").getHeap();
        return (globalDefs == null ? "" : "defs: " + globalDefs + "; ") + "pre: " + originalPres
            + (originalFreePres.get(heap) != null
                    && !originalFreePres.get(heap).equals(tb.tt())
                            ? "free pre: " + originalFreePres
                            : "")
            + "; mby: " + originalMby + "; post: " + originalPosts
            + (originalFreePosts.get(heap) != null
                    && !originalFreePosts.get(heap).equals(
                        RENAMING_TERM_PROPERTY)
                                ? "free post: " + originalFreePosts
                                : "")
            + "; modifiable: " + originalModifiables + "; hasModifiable: " + hasRealModifiable
            + (originalAxioms != null && !originalAxioms.isEmpty() ? ("; axioms: " + originalAxioms)
                    : "")
            + "; termination: " + getModalityKind() + "; transaction: "
            + transactionApplicableContract();
    }

    @Override
    public final ContractPO createProofObl(InitConfig initConfig) {
        return (ContractPO) createProofObl(initConfig, this);
    }

    @Override
    public @Nullable ProofOblInput getProofObl(Services services) {
        return services.getSpecificationRepository().getPO(this);
    }

    @Override
    public ProofOblInput createProofObl(InitConfig initConfig, Contract contract) {
        return new FunctionalOperationContractPO(initConfig,
            (FunctionalOperationContract) contract);
    }

    @Override
    public ProofOblInput createProofObl(InitConfig initConfig, Contract contract,
            boolean addSymbolicExecutionLabel) {
        return new FunctionalOperationContractPO(initConfig, (FunctionalOperationContract) contract,
            false, addSymbolicExecutionLabel);
    }

    @Override
    public String getDisplayName() {
        return ContractFactory.generateDisplayName(Objects.requireNonNull(baseName,
            "baseName must be set"), kjt, pm, specifiedIn, id);
    }

    @Override
    public @Nullable ModifierKind getVisibility() {
        assert false; // this is currently not applicable for contracts
        return null;
    }

    @Override
    public boolean transactionApplicableContract() {
        return transaction;
    }

    @Override
    public FunctionalOperationContract setID(int newId) {
        return new FunctionalOperationContractImpl(baseName, null, kjt, pm, specifiedIn,
            modalityKind,
            originalPres, originalFreePres, originalMby, originalPosts, originalFreePosts,
            originalAxioms, originalModifiables, originalFreeModifiables, originalDeps,
            hasRealModifiable,
            hasRealFreeModifiable, originalSelfVar, originalParamVars, originalResultVar,
            originalExcVar, originalAtPreVars, globalDefs, newId, toBeSaved, transaction, services);
    }

    @Override
    public Contract setTarget(KeYJavaType newKJT, IObserverFunction newPM) {
        assert newPM instanceof IProgramMethod;
        return new FunctionalOperationContractImpl(baseName, null, newKJT, (IProgramMethod) newPM,
            specifiedIn, modalityKind, originalPres, originalFreePres, originalMby, originalPosts,
            originalFreePosts, originalAxioms, originalModifiables, originalFreeModifiables,
            originalDeps,
            hasRealModifiable, hasRealFreeModifiable, originalSelfVar, originalParamVars,
            originalResultVar, originalExcVar, originalAtPreVars, globalDefs, id,
            toBeSaved && newKJT.equals(kjt), transaction, services);
    }

    @Override
    public String getTypeName() {
        return ContractFactory.generateContractTypeName(Objects.requireNonNull(baseName,
            "baseName must be set"), kjt, pm, specifiedIn);
    }

    @Override
    public boolean hasSelfVar() {
        return originalSelfVar != null;
    }

    @Override
    public @Nullable String getBaseName() {
        return baseName;
    }

    @Override
    public JTerm getPre() {
        assert originalPres.size() == 1
                : "information flow extension not compatible with multi-heap setting";
        return originalPres.values().iterator().next();
    }

    @Override
    public JTerm getPost() {
        assert originalPosts.size() == 1
                : "information flow extension not compatible with multi-heap setting";
        return originalPosts.values().iterator().next();
    }

    @Override
    public JTerm getModifiable() {
        return originalModifiables.values().iterator().next();
    }

    @Override
    public @Nullable JTerm getMby() {
        return originalMby;
    }

    @Override
    public @Nullable JTerm getSelf() {
        if (originalSelfVar == null) {
            assert pm.isStatic() : "missing self variable in non-static method contract";
            return null;
        }
        return tb.var(originalSelfVar);
    }

    @Override
    public boolean hasResultVar() {
        return originalResultVar != null;
    }

    @Override
    public @Nullable ImmutableList<JTerm> getParams() {
        if (originalParamVars == null) {
            return null;
        }
        return tb.var(originalParamVars);
    }

    @Override
    public @Nullable JTerm getResult() {
        if (originalResultVar == null) {
            return null;
        }
        return tb.var(originalResultVar);
    }

    @Override
    public @Nullable JTerm getExc() {
        if (originalExcVar == null) {
            return null;
        }
        return tb.var(originalExcVar);
    }

    @Override
    public KeYJavaType getSpecifiedIn() {
        return specifiedIn;
    }

    @Override
    public OriginalVariables getOrigVars() {
        Map<LocationVariable, LocationVariable> atPreVars =
            new LinkedHashMap<>();
        for (LocationVariable h : originalAtPreVars.keySet()) {
            atPreVars.put(h, originalAtPreVars.get(h));
        }
        return new OriginalVariables(originalSelfVar, originalResultVar, originalExcVar, atPreVars,
            originalParamVars);
    }

    @Override
    public IProgramMethod getProgramMethod() {
        return pm;
    }
}

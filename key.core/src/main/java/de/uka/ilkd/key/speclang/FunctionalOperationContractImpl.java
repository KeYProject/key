/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang;

import java.util.*;
import java.util.Map.Entry;
import java.util.function.UnaryOperator;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.modifier.VisibilityModifier;
import de.uka.ilkd.key.java.expression.operator.CopyAssignment;
import de.uka.ilkd.key.java.reference.MethodReference;
import de.uka.ilkd.key.java.statement.CatchAllStatement;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.proof.init.ContractPO;
import de.uka.ilkd.key.proof.init.FunctionalOperationContractPO;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProofOblInput;

import org.key_project.logic.Named;
import org.key_project.logic.SyntaxElement;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.java.MapUtil;

import static de.uka.ilkd.key.logic.equality.RenamingTermProperty.RENAMING_TERM_PROPERTY;
import static de.uka.ilkd.key.util.Assert.assertEqualSort;
import static de.uka.ilkd.key.util.Assert.assertSubSort;

/**
 * Standard implementation of the OperationContract interface.
 */
public class FunctionalOperationContractImpl implements FunctionalOperationContract {

    final String baseName;
    final String name;
    final KeYJavaType kjt;
    final IProgramMethod pm;
    final KeYJavaType specifiedIn;
    final Modality.JavaModalityKind modalityKind;
    /**
     * The original precondition terms.
     */
    final Map<LocationVariable, Term> originalPres;
    /**
     * The original free/unchecked precondition terms.
     */
    final Map<LocationVariable, Term> originalFreePres;
    final Term originalMby;
    /**
     * The original postcondition terms.
     */
    final Map<LocationVariable, Term> originalPosts;
    /**
     * The original free/unchecked postcondition terms.
     */
    final Map<LocationVariable, Term> originalFreePosts;
    /**
     * The original axiom terms.
     */
    final Map<LocationVariable, Term> originalAxioms;
    /**
     * The original modifiable clause terms.
     */
    final Map<LocationVariable, Term> originalModifiables;
    /**
     * The original modifiable_free clause terms.
     */
    final Map<LocationVariable, Term> originalFreeModifiables;
    final Map<LocationVariable, Term> originalDeps;
    final LocationVariable originalSelfVar;
    final ImmutableList<LocationVariable> originalParamVars;
    final LocationVariable originalResultVar;
    final LocationVariable originalExcVar;
    /**
     * The mapping of the pre-heap variables.
     */
    final Map<LocationVariable, LocationVariable> originalAtPreVars;
    final Term globalDefs;
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
     * future. Please use the factory methods in {@link de.uka.ilkd.key.speclang.ContractFactory}.
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
    FunctionalOperationContractImpl(String baseName, String name, KeYJavaType kjt,
            IProgramMethod pm, KeYJavaType specifiedIn, Modality.JavaModalityKind modalityKind,
            Map<LocationVariable, Term> pres, Map<LocationVariable, Term> freePres,
            Term mby,
            Map<LocationVariable, Term> posts, Map<LocationVariable, Term> freePosts,
            Map<LocationVariable, Term> axioms,
            Map<LocationVariable, Term> modifiables, Map<LocationVariable, Term> freeModifiables,
            Map<LocationVariable, Term> accessibles,
            Map<LocationVariable, Boolean> hasRealModifiable,
            Map<LocationVariable, Boolean> hasRealFreeModifiable,
            LocationVariable selfVar, ImmutableList<LocationVariable> paramVars,
            LocationVariable resultVar, LocationVariable excVar,
            Map<LocationVariable, LocationVariable> atPreVars, Term globalDefs, int id,
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
                    : "non-null result variable for void method or constructor " + pm
                        + " with return type " + pm.getReturnType();
        }
        assert pm.isModel() || excVar != null;
        assert atPreVars.size() != 0;
        assert services != null;
        this.services = services;
        this.tb = services.getTermBuilder();
        this.baseName = baseName;
        this.name = name != null ? name
                : ContractFactory.generateContractName(baseName, kjt, pm, specifiedIn, id);
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
    public FunctionalOperationContract map(UnaryOperator<Term> op, Services services) {
        Map<LocationVariable, Term> newPres = originalPres.entrySet().stream()
                .collect(MapUtil.collector(Map.Entry::getKey, entry -> op.apply(entry.getValue())));
        Map<LocationVariable, Term> newFreePres = originalFreePres.entrySet().stream()
                .collect(MapUtil.collector(Map.Entry::getKey, entry -> op.apply(entry.getValue())));
        Term newMby = op.apply(originalMby);
        Map<LocationVariable, Term> newPosts = originalPosts.entrySet().stream()
                .collect(MapUtil.collector(Map.Entry::getKey, entry -> op.apply(entry.getValue())));
        Map<LocationVariable, Term> newFreePosts = originalFreePosts.entrySet().stream()
                .collect(MapUtil.collector(Map.Entry::getKey, entry -> op.apply(entry.getValue())));
        Map<LocationVariable, Term> newAxioms = originalAxioms == null ? null
                : originalAxioms.entrySet().stream().collect(
                    MapUtil.collector(Map.Entry::getKey, entry -> op.apply(entry.getValue())));
        Map<LocationVariable, Term> newModifiables = originalModifiables.entrySet().stream()
                .collect(MapUtil.collector(Map.Entry::getKey, entry -> op.apply(entry.getValue())));
        Map<LocationVariable, Term> newFreeModifiables =
            originalFreeModifiables.entrySet().stream().collect(
                MapUtil.collector(Map.Entry::getKey, entry -> op.apply(entry.getValue())));
        Map<LocationVariable, Term> newAccessibles = originalDeps.entrySet().stream()
                .collect(MapUtil.collector(Map.Entry::getKey, entry -> op.apply(entry.getValue())));
        Term newGlobalDefs = op.apply(globalDefs);

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
    protected Map<LocationVariable, LocationVariable> getReplaceMap(LocationVariable selfVar,
            ImmutableList<LocationVariable> paramVars, LocationVariable resultVar,
            LocationVariable excVar, Map<LocationVariable, LocationVariable> atPreVars,
            Services services) {
        final Map<LocationVariable, LocationVariable> result = new LinkedHashMap<>();

        // self
        if (selfVar != null) {
            assertSubSort(selfVar, originalSelfVar);
            result.put(originalSelfVar, selfVar);
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
            assertSubSort(resultVar, originalResultVar);
            result.put(originalResultVar, resultVar);
        }

        // exception
        if (excVar != null) {
            assertEqualSort(originalExcVar, excVar);
            result.put(originalExcVar, excVar);
        }

        if (atPreVars != null) {
            final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
            for (LocationVariable h : heapLDT.getAllHeaps()) {
                if (atPreVars.get(h) != null) {
                    assertEqualSort(originalAtPreVars.get(h), atPreVars.get(h));
                    result.put(originalAtPreVars.get(h), atPreVars.get(h));
                }
            }
        }

        return result;
    }

    @Deprecated
    protected Map<Term, Term> getReplaceMap(LocationVariable heap, Term heapTerm, Term selfTerm,
            ImmutableList<Term> paramTerms, Services services) {
        return getReplaceMap(heap, heapTerm, selfTerm, paramTerms, null, null, null, services);
    }

    @Deprecated
    protected Map<Term, Term> getReplaceMap(LocationVariable heap, Term heapTerm, Term selfTerm,
            ImmutableList<Term> paramTerms, Term resultTerm, Term excTerm, Term atPre,
            Services services) {
        Map<LocationVariable, Term> heapTerms = new LinkedHashMap<>();
        heapTerms.put(heap, heapTerm);
        Map<LocationVariable, Term> atPres = new LinkedHashMap<>();
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
     */
    protected Map<Term, Term> getReplaceMap(Map<LocationVariable, Term> heapTerms, Term selfTerm,
            ImmutableList<Term> paramTerms, Term resultTerm, Term excTerm,
            Map<LocationVariable, Term> atPres, Services services) {
        final Map<Term, Term> result = new LinkedHashMap<>();

        // heaps
        for (LocationVariable heap : heapTerms.keySet()) {
            final Term heapTerm = heapTerms.get(heap);
            assert heapTerm == null || heapTerm.sort()
                    .equals(services.getTypeConverter().getHeapLDT().targetSort());
            result.put(tb.var(heap), heapTerm);
        }

        // self
        if (selfTerm != null) {
            assertSubSort(selfTerm, originalSelfVar);
            result.put(tb.var(originalSelfVar), selfTerm);
        }

        // parameters
        if (paramTerms != null) {
            assert originalParamVars.size() == paramTerms.size();
            final Iterator<LocationVariable> it1 = originalParamVars.iterator();
            final Iterator<Term> it2 = paramTerms.iterator();
            while (it1.hasNext()) {
                LocationVariable originalParamVar = it1.next();
                Term paramTerm = it2.next();
                // TODO: what does this mean?
                assert paramTerm.sort().extendsTrans(originalParamVar.sort());
                result.put(tb.var(originalParamVar), paramTerm);
            }
        }

        // result
        if (resultTerm != null) {
            assertSubSort(resultTerm, originalResultVar);
            result.put(tb.var(originalResultVar), resultTerm);
        }

        // exception
        if (excTerm != null) {
            assertEqualSort(originalExcVar, excTerm);
            result.put(tb.var(originalExcVar), excTerm);
        }

        if (atPres != null) {
            final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
            for (LocationVariable h : heapLDT.getAllHeaps()) {
                if (atPres.get(h) != null) {
                    assertEqualSort(originalAtPreVars.get(h), atPres.get(h));
                    result.put(tb.var(originalAtPreVars.get(h)), atPres.get(h));
                }
            }
        }
        return result;
    }

    /** Make sure ghost parameters appear in the list of parameter variables. */
    private ImmutableList<LocationVariable> addGhostParams(
            ImmutableList<LocationVariable> paramVars) {
        // make sure ghost parameters are present
        ImmutableList<LocationVariable> ghostParams = ImmutableSLList.nil();
        for (LocationVariable param : originalParamVars) {
            if (param.isGhost()) {
                ghostParams = ghostParams.append(param);
            }
        }
        paramVars = paramVars.append(ghostParams);
        return paramVars;
    }

    /** Make sure ghost parameters appear in the list of parameter variables. */
    private ImmutableList<Term> addGhostParamTerms(ImmutableList<Term> paramVars) {
        // make sure ghost parameters are present
        ImmutableList<Term> ghostParams = ImmutableSLList.nil();
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
    public Term getPre(LocationVariable heap, LocationVariable selfVar,
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
    public Term getPre(List<LocationVariable> heapContext, LocationVariable selfVar,
            ImmutableList<LocationVariable> paramVars,
            Map<LocationVariable, LocationVariable> atPreVars, Services services) {
        Term result = null;
        for (LocationVariable heap : heapContext) {
            final Term p = getPre(heap, selfVar, paramVars, atPreVars, services);
            if (result == null) {
                result = p;
            } else {
                result = tb.and(result, p);
            }
        }
        return result;
    }

    @Override
    public Term getPre(LocationVariable heap, Term heapTerm, Term selfTerm,
            ImmutableList<Term> paramTerms, Map<LocationVariable, Term> atPres, Services services) {
        assert heapTerm != null;
        assert (selfTerm == null) == (originalSelfVar == null);
        assert paramTerms != null;
        paramTerms = addGhostParamTerms(paramTerms);
        assert paramTerms.size() == originalParamVars.size();
        assert services != null;

        final Map<LocationVariable, Term> heapTerms = new LinkedHashMap<>();
        heapTerms.put(heap, heapTerm);

        final Map<Term, Term> replaceMap =
            getReplaceMap(heapTerms, selfTerm, paramTerms, null, null, atPres, services);
        final OpReplacer or =
            new OpReplacer(replaceMap, services.getTermFactory(), services.getProof());
        return or.replace(originalPres.get(heap));
    }

    @Override
    public Term getPre(List<LocationVariable> heapContext, Map<LocationVariable, Term> heapTerms,
            Term selfTerm, ImmutableList<Term> paramTerms, Map<LocationVariable, Term> atPres,
            Services services) {
        Term result = null;
        for (LocationVariable heap : heapContext) {
            final Term p =
                getPre(heap, heapTerms.get(heap), selfTerm, paramTerms, atPres, services);
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
    public Term getFreePre(LocationVariable heap, LocationVariable selfVar,
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
    public Term getFreePre(List<LocationVariable> heapContext, LocationVariable selfVar,
            ImmutableList<LocationVariable> paramVars,
            Map<LocationVariable, LocationVariable> atPreVars, Services services) {
        Term result = null;
        for (LocationVariable heap : heapContext) {
            final Term p = getFreePre(heap, selfVar, paramVars, atPreVars, services);
            if (result == null) {
                result = p;
            } else if (p != null) {
                result = tb.and(result, p);
            }
        }
        return result;
    }

    @Override
    public Term getFreePre(LocationVariable heap, Term heapTerm, Term selfTerm,
            ImmutableList<Term> paramTerms, Map<LocationVariable, Term> atPres, Services services) {
        assert heapTerm != null;
        assert (selfTerm == null) == (originalSelfVar == null);
        assert paramTerms != null;
        paramTerms = addGhostParamTerms(paramTerms);
        assert paramTerms.size() == originalParamVars.size();
        assert services != null;

        final Map<LocationVariable, Term> heapTerms = new LinkedHashMap<>();
        heapTerms.put(heap, heapTerm);

        final Map<Term, Term> replaceMap =
            getReplaceMap(heapTerms, selfTerm, paramTerms, null, null, atPres, services);
        final OpReplacer or =
            new OpReplacer(replaceMap, services.getTermFactory(), services.getProof());
        return or.replace(originalFreePres.get(heap));
    }

    @Override
    public Term getRequires(LocationVariable heap) {
        return originalPres.get(heap);
    }

    @Override
    public Term getEnsures(LocationVariable heap) {
        return originalPosts.get(heap);
    }

    @Override
    public Term getModifiable(LocationVariable heap) {
        return originalModifiables.get(heap);
    }

    @Override
    public Term getAccessible(LocationVariable heap) {
        return originalDeps.get(heap);
    }

    @Override
    public Term getMby(LocationVariable selfVar, ImmutableList<LocationVariable> paramVars,
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
    public Term getMby(Map<LocationVariable, Term> heapTerms, Term selfTerm,
            ImmutableList<Term> paramTerms, Map<LocationVariable, Term> atPres, Services services) {
        assert heapTerms != null;
        assert (selfTerm == null) == (originalSelfVar == null);
        assert paramTerms != null;
        paramTerms = addGhostParamTerms(paramTerms);
        assert paramTerms.size() == originalParamVars.size();
        assert services != null;
        final Map<Term, Term> replaceMap =
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
            NotationInfo.DEFAULT_PRETTY_SYNTAX, NotationInfo.DEFAULT_UNICODE_ENABLED);
    }

    public static String getText(FunctionalOperationContract contract,
            ImmutableList<Term> contractParams, Term resultTerm, Term contractSelf, Term excTerm,
            LocationVariable baseHeap, Term baseHeapTerm, List<LocationVariable> heapContext,
            Map<LocationVariable, Term> atPres, boolean includeHtmlMarkup, Services services,
            boolean usePrettyPrinting, boolean useUnicodeSymbols) {
        Operator originalSelfVar = contractSelf != null ? contractSelf.op() : null;
        Operator originalResultVar = resultTerm != null ? resultTerm.op() : null;
        final TermBuilder tb = services.getTermBuilder();

        Map<LocationVariable, Term> heapTerms = new LinkedHashMap<>();
        for (LocationVariable h : heapContext) {
            heapTerms.put(h, tb.var(h));
        }

        Term originalMby = contract.hasMby()
                ? contract.getMby(heapTerms, contractSelf, contractParams, atPres, services)
                : null;

        Map<LocationVariable, Term> originalModifiables = new HashMap<>();
        for (LocationVariable heap : heapContext) {
            Term m =
                contract.getModifiable(heap, tb.var(heap), contractSelf, contractParams, services);
            originalModifiables.put(heap, m);
        }

        Map<LocationVariable, Boolean> hasRealModifiable =
            new HashMap<>();
        for (LocationVariable heap : heapContext) {
            hasRealModifiable.put(heap, contract.hasModifiable(heap));
        }

        Term globalDefs =
            contract.getGlobalDefs(baseHeap, baseHeapTerm, contractSelf, contractParams, services);

        Map<LocationVariable, Term> originalPres = new HashMap<>();
        for (LocationVariable heap : heapContext) {
            Term preTerm = contract.getPre(heap, heapTerms.get(heap), contractSelf, contractParams,
                atPres, services);
            originalPres.put(heap, preTerm);
        }

        Map<LocationVariable, Term> originalFreePres = new HashMap<>();
        for (LocationVariable heap : heapContext) {
            Term freePreTerm = contract.getFreePre(heap, heapTerms.get(heap), contractSelf,
                contractParams, atPres, services);
            originalFreePres.put(heap, freePreTerm);
        }

        Map<LocationVariable, Term> originalPosts = new HashMap<>();
        for (LocationVariable heap : heapContext) {
            Term p = contract.getPost(heap, heapTerms.get(heap), contractSelf, contractParams,
                resultTerm, excTerm, atPres, services);
            originalPosts.put(heap, p);
        }

        Map<LocationVariable, Term> originalFreePosts = new HashMap<>();
        for (LocationVariable heap : heapContext) {
            Term p = contract.getFreePost(heap, heapTerms.get(heap), contractSelf, contractParams,
                resultTerm, excTerm, atPres, services);
            originalFreePosts.put(heap, p);
        }

        Map<LocationVariable, LocationVariable> atPresVars =
            new HashMap<>();
        for (Entry<LocationVariable, Term> entry : atPres.entrySet()) {
            if (entry.getValue() != null) {
                atPresVars.put(entry.getKey(), (LocationVariable) entry.getValue().op());
            } else {
                atPresVars.put(entry.getKey(), null);
            }
        }

        Map<LocationVariable, Term> originalAxioms = new HashMap<>();
        for (LocationVariable heap : heapContext) {
            Term p = contract.getRepresentsAxiom(heap, heapTerms.get(heap), contractSelf,
                contractParams, resultTerm, excTerm, atPres, services);
            originalAxioms.put(heap, p);
        }

        return getText(contract.getTarget(), originalResultVar, originalSelfVar, contractParams,
            (LocationVariable) excTerm.op(), contract.hasMby(), originalMby, originalModifiables,
            hasRealModifiable, globalDefs, originalPres, originalFreePres, originalPosts,
            originalFreePosts, originalAxioms, contract.getModalityKind(),
            contract.transactionApplicableContract(), includeHtmlMarkup, services,
            usePrettyPrinting, useUnicodeSymbols);
    }


    private static String getSignatureText(IProgramMethod pm, Operator originalResultVar,
            Operator originalSelfVar, ImmutableList<? extends SyntaxElement> originalParamVars,
            LocationVariable originalExcVar, Services services, boolean usePrettyPrinting,
            boolean useUnicodeSymbols) {
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
            } else if (subst instanceof Term) {
                sig.append(LogicPrinter.quickPrintTerm((Term) subst, services, usePrettyPrinting,
                    useUnicodeSymbols)).append(", ");
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
            Services services, boolean usePrettyPrinting, boolean useUnicodeSymbols, String clause,
            LocationVariable h, final Term clauseTerm) {
        final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
        final LocationVariable baseHeap = heapLDT.getHeap();

        String printClause =
            LogicPrinter.quickPrintTerm(clauseTerm, services, usePrettyPrinting, useUnicodeSymbols);
        clause = clause + (includeHtmlMarkup ? "<br><b>" : "\n") + text
                + (h == baseHeap ? "" : "[" + h + "]") + (includeHtmlMarkup ? "</b> " : ": ")
                + (includeHtmlMarkup ? LogicPrinter.escapeHTML(printClause, false)
                        : printClause);
        return clause;
    }

    private static String getClauseText(final String text,
            Map<LocationVariable, Term> originalClause, boolean includeHtmlMarkup,
            Services services, boolean usePrettyPrinting, boolean useUnicodeSymbols) {
        String clause = "";
        final TermBuilder tb = services.getTermBuilder();
        final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();

        for (LocationVariable h : heapLDT.getAllHeaps()) {
            Term clauseTerm = originalClause.get(h);
            if (clauseTerm != null && !clauseTerm.equals(tb.tt())) {
                clauseTerm = includeHtmlMarkup ? tb.unlabelRecursive(clauseTerm) : clauseTerm;
                clause = printClauseText(text, includeHtmlMarkup, services, usePrettyPrinting,
                    useUnicodeSymbols, clause, h, clauseTerm);
            }
        }
        return clause;
    }

    private static String getGlobalUpdatesText(Term globalDefs, boolean includeHtmlMarkup,
            Services services, boolean usePrettyPrinting, boolean useUnicodeSymbols) {
        String globalUpdates = "";
        final TermBuilder tb = services.getTermBuilder();
        if (globalDefs != null) {
            globalDefs = includeHtmlMarkup ? tb.unlabelRecursive(globalDefs) : globalDefs;
            final String printUpdates = LogicPrinter.quickPrintTerm(globalDefs, services,
                usePrettyPrinting, useUnicodeSymbols);
            globalUpdates = (includeHtmlMarkup ? "<br><b>" : "\n") + "defs"
                + (includeHtmlMarkup ? "</b> " : ": ")
                + (includeHtmlMarkup ? LogicPrinter.escapeHTML(printUpdates, false)
                        : printUpdates.trim());
        }
        return globalUpdates;
    }

    private static String getModifiableText(Map<LocationVariable, Term> originalModifiables,
            Map<LocationVariable, Boolean> hasRealModifiable, boolean includeHtmlMarkup,
            Services services, boolean usePrettyPrinting, boolean useUnicodeSymbols) {
        String modifiables = "";
        final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();

        for (LocationVariable h : heapLDT.getAllHeaps()) {
            final Term modifiableTerm = originalModifiables.get(h);
            if (modifiableTerm != null) {
                modifiables =
                    printClauseText("modifiable", includeHtmlMarkup, services, usePrettyPrinting,
                        useUnicodeSymbols, modifiables, h, modifiableTerm);
                if (!hasRealModifiable.get(h)) {
                    modifiables =
                        modifiables + (includeHtmlMarkup ? "<b>" : "") + ", creates no new objects"
                            + (includeHtmlMarkup ? "</b>" : "");
                }
            }
        }
        return modifiables;
    }

    private static String getPostText(Map<LocationVariable, Term> originalPosts,
            Map<LocationVariable, Term> originalAxioms, boolean includeHtmlMarkup,
            Services services, boolean usePrettyPrinting, boolean useUnicodeSymbols) {
        String posts = getClauseText("post", originalPosts, includeHtmlMarkup, services,
            usePrettyPrinting, useUnicodeSymbols);
        if (originalAxioms != null) {
            posts = posts + getClauseText("axiom", originalAxioms, includeHtmlMarkup, services,
                usePrettyPrinting, useUnicodeSymbols);
        }
        return posts;
    }

    private static String getText(IProgramMethod pm, Operator originalResultVar,
            Operator originalSelfVar, ImmutableList<? extends SyntaxElement> originalParamVars,
            LocationVariable originalExcVar, boolean hasMby, Term originalMby,
            Map<LocationVariable, Term> originalModifiables,
            Map<LocationVariable, Boolean> hasRealModifiable, Term globalDefs,
            Map<LocationVariable, Term> originalPres, Map<LocationVariable, Term> originalFreePres,
            Map<LocationVariable, Term> originalPosts,
            Map<LocationVariable, Term> originalFreePosts,
            Map<LocationVariable, Term> originalAxioms, Modality.JavaModalityKind modalityKind,
            boolean transaction,
            boolean includeHtmlMarkup, Services services, boolean usePrettyPrinting,
            boolean useUnicodeSymbols) {
        final String sig = getSignatureText(pm, originalResultVar, originalSelfVar,
            originalParamVars, originalExcVar, services, usePrettyPrinting, useUnicodeSymbols);

        final String mby = hasMby
                ? LogicPrinter.quickPrintTerm(originalMby, services, usePrettyPrinting,
                    useUnicodeSymbols)
                : null;

        final String modifiables =
            getModifiableText(originalModifiables, hasRealModifiable, includeHtmlMarkup,
                services, usePrettyPrinting, useUnicodeSymbols);

        final String globalUpdates = getGlobalUpdatesText(globalDefs, includeHtmlMarkup, services,
            usePrettyPrinting, useUnicodeSymbols);

        final String pres = getClauseText("pre", originalPres, includeHtmlMarkup, services,
            usePrettyPrinting, useUnicodeSymbols);

        final String freePres = getClauseText("free pre", originalFreePres, includeHtmlMarkup,
            services, usePrettyPrinting, useUnicodeSymbols);

        final String freePosts = getClauseText("free post", originalFreePosts, includeHtmlMarkup,
            services, usePrettyPrinting, useUnicodeSymbols);

        final String posts = getPostText(originalPosts, originalAxioms, includeHtmlMarkup, services,
            usePrettyPrinting, useUnicodeSymbols);

        final String clauses = globalUpdates + pres + freePres + posts + freePosts + modifiables;
        if (includeHtmlMarkup) {
            return "<html>" + "<i>" + LogicPrinter.escapeHTML(sig, false) + "</i>" + clauses
                + (hasMby ? "<br><b>measured-by</b> " + LogicPrinter.escapeHTML(mby, false) : "")
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
        final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
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
        sb.append("    ").append(originalExcVar.proofToString());
        sb.append("    ").append(originalAtPreVars.get(baseHeap).proofToString());
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
            callStatement = new CopyAssignment(originalResultVar, mr);
        }
        final CatchAllStatement cas = new CatchAllStatement(new StatementBlock(callStatement),
            (LocationVariable) originalExcVar);
        final StatementBlock sblock = new StatementBlock(cas);
        final JavaBlock jb = JavaBlock.createJavaBlock(sblock);

        // print contract term
        final Term update = tb.tf().createTerm(
            ElementaryUpdate.getInstance(originalAtPreVars.get(baseHeap)), tb.getBaseHeap());
        final Term modalityTerm =
            tb.prog(modalityKind, jb, originalPosts.get(baseHeap));
        final Term updateTerm =
            tb.tf().createTerm(UpdateApplication.UPDATE_APPLICATION, update, modalityTerm);
        final Term contractTerm =
            tb.tf().createTerm(Junctor.IMP, originalPres.get(baseHeap), updateTerm);
        final LogicPrinter lp = LogicPrinter.purePrinter(new NotationInfo(), null);
        lp.printTerm(contractTerm);
        sb.append(lp.result());

        // print modifiable
        lp.reset();
        lp.printTerm(originalModifiables.get(baseHeap));
        sb.append("  \\modifiable ").append(lp.result());

        sb.append("};\n");
        return sb.toString();
    }

    @Override
    public Modality.JavaModalityKind getModalityKind() {
        return modalityKind;
    }

    @Override
    public Term getPost(LocationVariable heap, LocationVariable selfVar,
            ImmutableList<LocationVariable> paramVars, LocationVariable resultVar,
            LocationVariable excVar, Map<LocationVariable, LocationVariable> atPreVars,
            Services services) {
        assert (selfVar == null) == (originalSelfVar == null);
        assert paramVars != null;
        paramVars = addGhostParams(paramVars);
        assert paramVars.size() == originalParamVars.size();
        assert (resultVar == null) == (originalResultVar == null);
        assert pm.isModel() || excVar != null;
        assert atPreVars.size() != 0;
        assert services != null;
        final Map<LocationVariable, LocationVariable> replaceMap =
            getReplaceMap(selfVar, paramVars, resultVar, excVar, atPreVars, services);
        final OpReplacer or =
            new OpReplacer(replaceMap, services.getTermFactory(), services.getProof());
        return or.replace(originalPosts.get(heap));
    }

    @Override
    public Term getPost(List<LocationVariable> heapContext, LocationVariable selfVar,
            ImmutableList<LocationVariable> paramVars, LocationVariable resultVar,
            LocationVariable excVar, Map<LocationVariable, LocationVariable> atPreVars,
            Services services) {
        Term result = null;
        for (LocationVariable heap : heapContext) {
            final Term p =
                getPost(heap, selfVar, paramVars, resultVar, excVar, atPreVars, services);
            if (result == null) {
                result = p;
            } else {
                result = tb.and(result, p);
            }
        }
        return result;

    }

    @Override
    public Term getPost(LocationVariable heap, Term heapTerm, Term selfTerm,
            ImmutableList<Term> paramTerms, Term resultTerm, Term excTerm,
            Map<LocationVariable, Term> atPres, Services services) {
        assert heapTerm != null;
        assert (selfTerm == null) == (originalSelfVar == null);
        assert paramTerms != null;
        paramTerms = addGhostParamTerms(paramTerms);
        assert paramTerms.size() == originalParamVars.size();
        assert (resultTerm == null) == (originalResultVar == null);
        assert pm.isModel() || excTerm != null;
        assert atPres.size() != 0;
        assert services != null;
        final Map<LocationVariable, Term> heapTerms = new LinkedHashMap<>();
        heapTerms.put(heap, heapTerm);

        final Map<Term, Term> replaceMap =
            getReplaceMap(heapTerms, selfTerm, paramTerms, resultTerm, excTerm, atPres, services);
        final OpReplacer or =
            new OpReplacer(replaceMap, services.getTermFactory(), services.getProof());
        return or.replace(originalPosts.get(heap));
    }

    @Override
    public Term getPost(List<LocationVariable> heapContext, Map<LocationVariable, Term> heapTerms,
            Term selfTerm, ImmutableList<Term> paramTerms, Term resultTerm, Term excTerm,
            Map<LocationVariable, Term> atPres, Services services) {
        Term result = null;
        for (LocationVariable heap : heapContext) {
            final Term p = getPost(heap, heapTerms.get(heap), selfTerm, paramTerms, resultTerm,
                excTerm, atPres, services);
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
    public Term getFreePost(LocationVariable heap, LocationVariable selfVar,
            ImmutableList<LocationVariable> paramVars, LocationVariable resultVar,
            LocationVariable excVar, Map<LocationVariable, LocationVariable> atPreVars,
            Services services) {
        assert (selfVar == null) == (originalSelfVar == null);
        assert paramVars != null;
        paramVars = addGhostParams(paramVars);
        assert paramVars.size() == originalParamVars.size();
        assert (resultVar == null) == (originalResultVar == null);
        assert pm.isModel() || excVar != null;
        assert atPreVars.size() != 0;
        assert services != null;
        final Map<LocationVariable, LocationVariable> replaceMap =
            getReplaceMap(selfVar, paramVars, resultVar, excVar, atPreVars, services);
        final OpReplacer or =
            new OpReplacer(replaceMap, services.getTermFactory(), services.getProof());
        return or.replace(originalFreePosts.get(heap));
    }

    @Override
    public Term getFreePost(LocationVariable heap, Term heapTerm, Term selfTerm,
            ImmutableList<Term> paramTerms, Term resultTerm, Term excTerm,
            Map<LocationVariable, Term> atPres, Services services) {
        assert heapTerm != null;
        assert (selfTerm == null) == (originalSelfVar == null);
        assert paramTerms != null;
        paramTerms = addGhostParamTerms(paramTerms);
        assert paramTerms.size() == originalParamVars.size();
        assert (resultTerm == null) == (originalResultVar == null);
        assert pm.isModel() || excTerm != null;
        assert atPres.size() != 0;
        assert services != null;
        final Map<LocationVariable, Term> heapTerms = new LinkedHashMap<>();
        heapTerms.put(heap, heapTerm);

        final Map<Term, Term> replaceMap =
            getReplaceMap(heapTerms, selfTerm, paramTerms, resultTerm, excTerm, atPres, services);
        final OpReplacer or =
            new OpReplacer(replaceMap, services.getTermFactory(), services.getProof());
        return or.replace(originalFreePosts.get(heap));
    }

    @Override
    public Term getFreePost(List<LocationVariable> heapContext,
            Map<LocationVariable, Term> heapTerms, Term selfTerm, ImmutableList<Term> paramTerms,
            Term resultTerm, Term excTerm, Map<LocationVariable, Term> atPres, Services services) {
        Term result = null;
        for (LocationVariable heap : heapContext) {
            final Term p = getFreePost(heap, heapTerms.get(heap), selfTerm, paramTerms, resultTerm,
                excTerm, atPres, services);
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
    public Term getFreePost(List<LocationVariable> heapContext, LocationVariable selfVar,
            ImmutableList<LocationVariable> paramVars, LocationVariable resultVar,
            LocationVariable excVar, Map<LocationVariable, LocationVariable> atPreVars,
            Services services) {
        Term result = null;
        for (LocationVariable heap : heapContext) {
            final Term p =
                getFreePost(heap, selfVar, paramVars, resultVar, excVar, atPreVars, services);
            if (result == null) {
                result = p;
            } else {
                result = tb.and(result, p);
            }
        }
        return result;

    }

    @Override
    public Term getRepresentsAxiom(LocationVariable heap, LocationVariable selfVar,
            ImmutableList<LocationVariable> paramVars, LocationVariable resultVar,
            Map<LocationVariable, LocationVariable> atPreVars, Services services) {
        assert (selfVar == null) == (originalSelfVar == null) : "Illegal instantiation:"
            + (originalSelfVar == null
                    ? "this is a static contract, instantiated with self variable '" + selfVar + "'"
                    : "this is an instance contract, instantiated without a self variable");
        assert paramVars != null;
        assert paramVars.size() == originalParamVars.size();
        assert (resultVar == null) == (originalResultVar == null);
        assert atPreVars.size() != 0;
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
    public Term getRepresentsAxiom(LocationVariable heap, Term heapTerm, Term selfTerm,
            ImmutableList<Term> paramTerms, Term resultTerm, Term excTerm,
            Map<LocationVariable, Term> atPres, Services services) {
        assert heapTerm != null;
        assert (selfTerm == null) == (originalSelfVar == null);
        assert paramTerms != null;
        paramTerms = addGhostParamTerms(paramTerms);
        assert paramTerms.size() == originalParamVars.size();
        assert (resultTerm == null) == (originalResultVar == null);
        assert pm.isModel() || excTerm != null;
        assert atPres.size() != 0;
        assert services != null;
        final Map<LocationVariable, Term> heapTerms = new LinkedHashMap<>();
        heapTerms.put(heap, heapTerm);

        final Map<Term, Term> replaceMap =
            getReplaceMap(heapTerms, selfTerm, paramTerms, resultTerm, excTerm, atPres, services);
        final OpReplacer or =
            new OpReplacer(replaceMap, services.getTermFactory(), services.getProof());
        return or.replace(originalAxioms.get(heap));
    }

    @Override
    public boolean isReadOnlyContract(Services services) {
        return originalModifiables.get(services.getTypeConverter().getHeapLDT().getHeap())
                .op() == services
                        .getTypeConverter().getLocSetLDT().getEmpty();
    }

    public Term getAnyModifiable(Term modifiable, LocationVariable selfVar,
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
    public Term getModifiable(LocationVariable heap, LocationVariable selfVar,
            ImmutableList<LocationVariable> paramVars, Services services) {
        return getAnyModifiable(this.originalModifiables.get(heap), selfVar, paramVars,
            services);
    }

    @Override
    public Term getFreeModifiable(LocationVariable heap, LocationVariable selfVar,
            ImmutableList<LocationVariable> paramVars, Services services) {
        return getAnyModifiable(this.originalFreeModifiables.get(heap), selfVar, paramVars,
            services);
    }

    private Term getAnyModifiable(LocationVariable heap, Term modifiable, Term heapTerm,
            Term selfTerm,
            ImmutableList<Term> paramTerms, Services services) {
        assert heapTerm != null;
        assert (selfTerm == null) == (originalSelfVar == null);
        assert paramTerms != null;
        paramTerms = addGhostParamTerms(paramTerms);
        assert paramTerms.size() == originalParamVars.size();
        assert services != null;

        final Map<LocationVariable, Term> heapTerms = new LinkedHashMap<>();
        heapTerms.put(heap, heapTerm);

        final Map<Term, Term> replaceMap =
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
    public Term getModifiable(LocationVariable heap, Term heapTerm, Term selfTerm,
            ImmutableList<Term> paramTerms, Services services) {
        return getAnyModifiable(heap, this.originalModifiables.get(heap), heapTerm, selfTerm,
            paramTerms,
            services);
    }

    @Override
    public Term getFreeModifiable(LocationVariable heap, Term heapTerm,
            Term selfTerm, ImmutableList<Term> paramTerms, Services services) {
        return getAnyModifiable(heap, this.originalFreeModifiables.get(heap), heapTerm, selfTerm,
            paramTerms,
            services);
    }

    @Override
    public Term getDep(LocationVariable heap, boolean atPre, LocationVariable selfVar,
            ImmutableList<LocationVariable> paramVars,
            Map<LocationVariable, LocationVariable> atPreVars, Services services) {
        assert (selfVar == null) == (originalSelfVar == null);
        assert paramVars != null;
        assert paramVars.size() == originalParamVars.size();
        assert services != null;
        Map<SyntaxElement, SyntaxElement> map = new LinkedHashMap<>();
        if (originalSelfVar != null) {
            map.put(originalSelfVar, selfVar);
        }
        for (LocationVariable originalParamVar : originalParamVars) {
            map.put(originalParamVar, paramVars.head());
            paramVars = paramVars.tail();
        }
        if (atPreVars != null && originalAtPreVars != null) {
            for (LocationVariable h : services.getTypeConverter().getHeapLDT().getAllHeaps()) {
                LocationVariable originalAtPreVar = originalAtPreVars.get(h);
                if (atPreVars.get(h) != null && originalAtPreVar != null) {
                    map.put(tb.var(atPre ? h : originalAtPreVar), tb.var(atPreVars.get(h)));
                }
            }
        }
        OpReplacer or = new OpReplacer(map, services.getTermFactory(), services.getProof());
        return or.replace(originalDeps.get(atPre ? originalAtPreVars.get(heap) : heap));
    }

    @Override
    public Term getDep(LocationVariable heap, boolean atPre, Term heapTerm, Term selfTerm,
            ImmutableList<Term> paramTerms, Map<LocationVariable, Term> atPres, Services services) {
        assert heapTerm != null;
        assert (selfTerm == null) == (originalSelfVar == null);
        assert paramTerms != null;
        assert paramTerms.size() == originalParamVars.size();
        assert services != null;
        Map<SyntaxElement, SyntaxElement> map = new LinkedHashMap<>();
        map.put(tb.var(heap), heapTerm);
        if (originalSelfVar != null) {
            map.put(tb.var(originalSelfVar), selfTerm);
        }
        for (LocationVariable originalParamVar : originalParamVars) {
            map.put(tb.var(originalParamVar), paramTerms.head());
            paramTerms = paramTerms.tail();
        }
        if (atPres != null && originalAtPreVars != null) {
            for (LocationVariable h : services.getTypeConverter().getHeapLDT().getAllHeaps()) {
                LocationVariable originalAtPreVar = originalAtPreVars.get(h);
                if (originalAtPreVar != null && atPres.get(h) != null) {
                    map.put(tb.var(originalAtPreVar), atPres.get(h));
                }
            }
        }
        OpReplacer or = new OpReplacer(map, services.getTermFactory(), services.getProof());
        return or.replace(originalDeps.get(atPre ? originalAtPreVars.get(heap) : heap));
    }

    @Override
    public Term getGlobalDefs() {
        return this.globalDefs;
    }

    @Override
    public Term getGlobalDefs(LocationVariable heap, Term heapTerm, Term selfTerm,
            ImmutableList<Term> paramTerms, Services services) {
        if (globalDefs == null) {
            return null;
        }
        assert heapTerm != null;
        assert (selfTerm == null) == (originalSelfVar == null);
        assert paramTerms != null;
        paramTerms = addGhostParamTerms(paramTerms);
        assert paramTerms.size() == originalParamVars.size();
        assert services != null;
        final Map<Term, Term> replaceMap =
            getReplaceMap(heap, heapTerm, selfTerm, paramTerms, services);
        final OpReplacer or =
            new OpReplacer(replaceMap, services.getTermFactory(), services.getProof());
        return or.replace(globalDefs);
    }

    @Override
    public String toString() {
        final LocationVariable heap =
            ((Services) services).getTypeConverter().getHeapLDT().getHeap();
        return (globalDefs == null ? "" : "defs: " + globalDefs + "; ") + "pre: " + originalPres
            + (originalFreePres.get(heap) != null
                    && !originalFreePres.get(heap).equalsModProperty(tb.tt(),
                        RENAMING_TERM_PROPERTY)
                                ? "free pre: " + originalFreePres
                                : "")
            + "; mby: " + originalMby + "; post: " + originalPosts
            + (originalFreePosts.get(heap) != null
                    && !originalFreePosts.get(heap).equalsModProperty(tb.tt(),
                        RENAMING_TERM_PROPERTY)
                                ? "free post: " + originalFreePosts
                                : "")
            + "; modifiable: " + originalModifiables + "; hasModifiable: " + hasRealModifiable
            + (originalAxioms != null && originalAxioms.size() > 0 ? ("; axioms: " + originalAxioms)
                    : "")
            + "; termination: " + getModalityKind() + "; transaction: "
            + transactionApplicableContract();
    }

    @Override
    public final ContractPO createProofObl(InitConfig initConfig) {
        return (ContractPO) createProofObl(initConfig, this);
    }

    @Override
    public ProofOblInput getProofObl(Services services) {
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
        return ContractFactory.generateDisplayName(baseName, kjt, pm, specifiedIn, id);
    }

    @Override
    public VisibilityModifier getVisibility() {
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
        return ContractFactory.generateContractTypeName(baseName, kjt, pm, specifiedIn);
    }

    @Override
    public boolean hasSelfVar() {
        return originalSelfVar != null;
    }

    @Override
    public String getBaseName() {
        return baseName;
    }

    @Override
    public Term getPre() {
        assert originalPres.values().size() == 1
                : "information flow extension not compatible with multi-heap setting";
        return originalPres.values().iterator().next();
    }

    @Override
    public Term getPost() {
        assert originalPosts.values().size() == 1
                : "information flow extension not compatible with multi-heap setting";
        return originalPosts.values().iterator().next();
    }

    @Override
    public Term getModifiable() {
        return originalModifiables.values().iterator().next();
    }

    @Override
    public Term getMby() {
        return originalMby;
    }

    @Override
    public Term getSelf() {
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
    public ImmutableList<Term> getParams() {
        if (originalParamVars == null) {
            return null;
        }
        return tb.var(originalParamVars);
    }

    @Override
    public Term getResult() {
        if (originalResultVar == null) {
            return null;
        }
        return tb.var(originalResultVar);
    }

    @Override
    public Term getExc() {
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
}

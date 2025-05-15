/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang;

import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.function.UnaryOperator;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.modifier.VisibilityModifier;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.proof.init.ContractPO;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.init.StrictDependencyContractPO;

import org.key_project.logic.SyntaxElement;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.java.MapUtil;

import static de.uka.ilkd.key.util.Assert.assertEqualSort;
import static de.uka.ilkd.key.util.Assert.assertSubSort;

/**
 * Standard implementation of the DependencyContract interface.
 */
public final class DependencyContractImpl implements DependencyContract {
    final String baseName;
    final String name;
    final KeYJavaType kjt;
    final IObserverFunction target;
    final KeYJavaType specifiedIn;
    final Map<LocationVariable, Term> originalPres;
    final Term originalMby;
    final Map<LocationVariable, Term> originalDeps;
    final Map<LocationVariable, Term> originalModifiables;
    final LocationVariable originalSelfVar;
    final ImmutableList<LocationVariable> originalParamVars;
    final Map<LocationVariable, LocationVariable> originalAtPreVars;
    final Term globalDefs;
    final int id;

    // -------------------------------------------------------------------------
    // constructors
    // -------------------------------------------------------------------------

    DependencyContractImpl(String baseName, String name, KeYJavaType kjt, IObserverFunction target,
            KeYJavaType specifiedIn, Map<LocationVariable, Term> pres, Term mby,
            Map<LocationVariable, Term> deps, Map<LocationVariable, Term> modifiables,
            LocationVariable selfVar,
            ImmutableList<LocationVariable> paramVars,
            Map<LocationVariable, LocationVariable> atPreVars, Term globalDefs, int id) {
        assert baseName != null;
        assert kjt != null;
        assert target != null;
        assert pres != null;
        assert deps != null : "cannot create contract " + baseName + " for " + target
            + " when no specification is given";
        assert (selfVar == null) == target.isStatic();
        assert paramVars != null;
        // This cannot be done properly for multiple heaps without access to services:
        // assert paramVars.size() == target.arity() - (target.isStatic() ? 1 : 2);
        assert target.getStateCount() > 0;
        this.baseName = baseName;
        this.name = name != null ? name
                : ContractFactory.generateContractName(baseName, kjt, target, specifiedIn, id);
        this.kjt = kjt;
        this.target = target;
        this.specifiedIn = specifiedIn;
        this.originalPres = pres;
        this.originalMby = mby;
        this.originalDeps = deps;
        this.originalModifiables = modifiables;
        this.originalSelfVar = selfVar;
        this.originalParamVars = paramVars;
        this.originalAtPreVars = atPreVars;
        this.globalDefs = globalDefs;
        this.id = id;
    }

    @Deprecated
    DependencyContractImpl(String baseName, KeYJavaType kjt, IObserverFunction target,
            KeYJavaType specifiedIn, Map<LocationVariable, Term> pres, Term mby,
            Map<LocationVariable, Term> deps, Map<LocationVariable, Term> modifiables,
            LocationVariable selfVar,
            ImmutableList<LocationVariable> paramVars,
            Map<LocationVariable, LocationVariable> atPreVars) {
        this(baseName, null, kjt, target, specifiedIn, pres, mby, deps, modifiables, selfVar,
            paramVars,
            atPreVars, null, INVALID_ID);
    }

    // -------------------------------------------------------------------------
    // public interface
    // -------------------------------------------------------------------------

    @Override
    public DependencyContract map(UnaryOperator<Term> op, Services services) {
        Map<LocationVariable, Term> newPres = originalPres.entrySet().stream()
                .collect(MapUtil.collector(Map.Entry::getKey, entry -> op.apply(entry.getValue())));
        Term newMby = op.apply(originalMby);
        Map<LocationVariable, Term> newDeps = originalDeps.entrySet().stream()
                .collect(MapUtil.collector(Map.Entry::getKey, entry -> op.apply(entry.getValue())));
        Map<LocationVariable, Term> newModifiables = originalModifiables.entrySet().stream()
                .collect(MapUtil.collector(Map.Entry::getKey, entry -> op.apply(entry.getValue())));

        return new DependencyContractImpl(baseName, name, kjt, target, specifiedIn, newPres, newMby,
            newDeps, newModifiables, originalSelfVar, originalParamVars, originalAtPreVars,
            globalDefs, id);
    }

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
    public IObserverFunction getTarget() {
        return target;
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
                    map.put(services.getTermBuilder().var(originalAtPreVar),
                        services.getTermBuilder().var(atPreVars.get(h)));
                }
            }
        }

        OpReplacer or = new OpReplacer(map, services.getTermFactory(), services.getProof());
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
                result = services.getTermBuilder().and(result, p);
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
        assert paramTerms.size() == originalParamVars.size();
        assert services != null;
        Map<SyntaxElement, SyntaxElement> map = new LinkedHashMap<>();
        map.put(services.getTermBuilder().var(heap), heapTerm);
        if (originalSelfVar != null) {
            map.put(services.getTermBuilder().var(originalSelfVar), selfTerm);
        }
        for (LocationVariable originalParamVar : originalParamVars) {
            map.put(services.getTermBuilder().var(originalParamVar), paramTerms.head());
            paramTerms = paramTerms.tail();
        }
        if (atPres != null && originalAtPreVars != null) {
            for (LocationVariable h : services.getTypeConverter().getHeapLDT().getAllHeaps()) {
                LocationVariable originalAtPreVar = originalAtPreVars.get(h);
                if (atPres.get(h) != null && originalAtPreVar != null) {
                    map.put(services.getTermBuilder().var(originalAtPreVar), atPres.get(h));
                }
            }
        }
        OpReplacer or = new OpReplacer(map, services.getTermFactory(), services.getProof());
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
            if (result == null) {
                result = p;
            } else {
                result = services.getTermBuilder().and(result, p);
            }
        }
        return result;
    }

    @Override
    public Term getRequires(LocationVariable heap) {
        return originalPres.get(heap);
    }

    @Override
    public Term getModifiable(LocationVariable heap) {
        // TODO(DD): implement
        throw new UnsupportedOperationException("Not applicable for dependency contracts.");
    }

    @Override
    public Term getAccessible(LocationVariable heap) {
        return originalDeps.get(heap);
    }

    @Override
    public Term getMby() {
        return this.originalMby;
    }

    @Override
    public Term getMby(LocationVariable selfVar, ImmutableList<LocationVariable> paramVars,
            Services services) {
        assert hasMby();
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
        OpReplacer or = new OpReplacer(map, services.getTermFactory(), services.getProof());
        return or.replace(originalMby);
    }

    @Override
    public Term getMby(Map<LocationVariable, Term> heapTerms, Term selfTerm,
            ImmutableList<Term> paramTerms, Map<LocationVariable, Term> atPres, Services services) {
        assert hasMby();
        assert heapTerms != null;
        assert (selfTerm == null) == (originalSelfVar == null);
        assert paramTerms != null;
        assert paramTerms.size() == originalParamVars.size();
        assert services != null;
        Map<SyntaxElement, SyntaxElement> map = new LinkedHashMap<>();
        for (LocationVariable heap : heapTerms.keySet()) {
            map.put(services.getTermBuilder().var(heap), heapTerms.get(heap));
        }
        if (originalSelfVar != null) {
            map.put(services.getTermBuilder().var(originalSelfVar), selfTerm);
        }
        for (LocationVariable originalParamVar : originalParamVars) {
            map.put(services.getTermBuilder().var(originalParamVar), paramTerms.head());
            paramTerms = paramTerms.tail();
        }
        if (atPres != null && originalAtPreVars != null) {
            for (LocationVariable h : services.getTypeConverter().getHeapLDT().getAllHeaps()) {
                LocationVariable originalAtPreVar = originalAtPreVars.get(h);
                if (atPres.get(h) != null && originalAtPreVar != null) {
                    map.put(services.getTermBuilder().var(originalAtPreVar), atPres.get(h));
                }
            }
        }
        OpReplacer or = new OpReplacer(map, services.getTermFactory(), services.getProof());
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
        StringBuilder pres = new StringBuilder();
        for (LocationVariable h : originalPres.keySet()) {
            Term originalPre = originalPres.get(h);
            if (originalPre != null) {
                pres.append("<b>pre[").append(h).append("]</b> ").append(LogicPrinter.escapeHTML(
                    LogicPrinter.quickPrintTerm(originalPre, services), false)).append("<br>");
            }
        }
        StringBuilder deps = new StringBuilder();
        for (LocationVariable h : originalDeps.keySet()) {
            if (h.name().toString().endsWith("AtPre") && target.getStateCount() == 1) {
                continue;
            }
            Term originalDep = originalDeps.get(h);
            if (originalDep != null) {
                deps.append("<b>dep[").append(h).append("]</b> ").append(LogicPrinter.escapeHTML(
                    LogicPrinter.quickPrintTerm(originalDep, services), false)).append("<br>");
            }
        }
        final String mby = hasMby() ? LogicPrinter.quickPrintTerm(originalMby, services) : null;

        if (includeHtmlMarkup) {
            return "<html>" + pres + deps
                + (mby != null ? "<br><b>measured-by</b> " + LogicPrinter.escapeHTML(mby, false)
                        : "")
                + "</html>";
        } else {
            return "pre: " + pres + "\ndep: " + deps + (hasMby() ? "\nmeasured-by: " + mby : "");
        }
    }

    @Override
    public boolean toBeSaved() {
        return false; // because dependency contracts currently cannot be
        // specified directly in DL
    }

    @Override
    public String proofToString(Services services) {
        assert false;
        return null;
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
                    map.put(services.getTermBuilder().var(atPre ? h : originalAtPreVar),
                        services.getTermBuilder().var(atPreVars.get(h)));
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
        map.put(services.getTermBuilder().var(heap), heapTerm);
        if (originalSelfVar != null) {
            map.put(services.getTermBuilder().var(originalSelfVar), selfTerm);
        }
        for (LocationVariable originalParamVar : originalParamVars) {
            map.put(services.getTermBuilder().var(originalParamVar), paramTerms.head());
            paramTerms = paramTerms.tail();
        }
        if (atPres != null && originalAtPreVars != null) {
            for (LocationVariable h : services.getTypeConverter().getHeapLDT().getAllHeaps()) {
                LocationVariable originalAtPreVar = originalAtPreVars.get(h);
                if (originalAtPreVar != null && atPres.get(h) != null) {
                    map.put(services.getTermBuilder().var(originalAtPreVar), atPres.get(h));
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
        assert false : "old clauses are not yet supported for dependency contracts";
        return null;
    }

    @Override
    public String toString() {
        return originalDeps.toString();
    }

    @Override
    public String getDisplayName() {
        return ContractFactory.generateDisplayName(baseName, kjt, target, specifiedIn, id);
    }

    @Override
    public VisibilityModifier getVisibility() {
        return null;
    }

    @Override
    public boolean transactionApplicableContract() {
        return false;
    }

    @Override
    public ProofOblInput createProofObl(InitConfig initConfig, Contract contract,
            boolean addSymbolicExecutionLabel) {
        if (addSymbolicExecutionLabel) {
            throw new IllegalStateException("Symbolic Execution API is not supported.");
        } else {
            return createProofObl(initConfig, contract);
        }
    }

    @Override
    public ProofOblInput createProofObl(InitConfig initConfig, Contract contract) {
        return new StrictDependencyContractPO(initConfig, (DependencyContract) contract);
    }

    @Override
    public ContractPO createProofObl(InitConfig initConfig) {
        return (ContractPO) createProofObl(initConfig, this);
    }

    @Override
    public ProofOblInput getProofObl(Services services) {
        return services.getSpecificationRepository().getPO(this);
    }

    @Override
    public DependencyContract setID(int newId) {
        return new DependencyContractImpl(baseName, null, kjt, target, specifiedIn, originalPres,
            originalMby, originalDeps, originalModifiables, originalSelfVar, originalParamVars,
            originalAtPreVars,
            globalDefs, newId);
    }

    @Override
    public Contract setTarget(KeYJavaType newKJT, IObserverFunction newPM) {
        return new DependencyContractImpl(baseName, null, newKJT, newPM, specifiedIn, originalPres,
            originalMby, originalDeps, originalModifiables, originalSelfVar, originalParamVars,
            originalAtPreVars,
            globalDefs, id);
    }

    @Override
    public String getTypeName() {
        return ContractFactory.generateContractTypeName(baseName, kjt, target, specifiedIn);
    }

    @Override
    public boolean hasSelfVar() {
        return originalSelfVar != null;
    }

    @Override
    public OriginalVariables getOrigVars() {
        Map<LocationVariable, LocationVariable> atPreVars = new LinkedHashMap<>();
        if (originalAtPreVars != null) {
            for (LocationVariable h : originalAtPreVars.keySet()) {
                atPreVars.put(h, originalAtPreVars.get(h));
            }
        }
        return new OriginalVariables(originalSelfVar, null, null, atPreVars, originalParamVars);
    }

    @Override
    public Term getModifiable(LocationVariable heapVar, LocationVariable selfVar,
            ImmutableList<LocationVariable> paramVars, Services services) {
        return getAnyModifiable(this.originalModifiables.get(heapVar), selfVar, paramVars,
            services);
    }

    // -------------------------------------------------------------------------
    // internal methods
    // -------------------------------------------------------------------------

    private Term getAnyModifiable(Term modifiable, LocationVariable selfVar,
            ImmutableList<LocationVariable> paramVars, Services services) {
        assert (selfVar == null) == (originalSelfVar == null);
        assert paramVars != null;
        paramVars = addGhostParams(paramVars);
        assert paramVars.size() == originalParamVars.size();
        assert services != null;
        final Map<LocationVariable, LocationVariable> replaceMap =
            getReplaceMap(selfVar, paramVars, null, null, null,
                services);
        final OpReplacer or =
            new OpReplacer(replaceMap, services.getTermFactory(), services.getProof());
        return or.replace(modifiable);
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
}

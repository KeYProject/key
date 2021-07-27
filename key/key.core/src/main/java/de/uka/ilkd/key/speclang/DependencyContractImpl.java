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
import java.util.List;
import java.util.Map;
import java.util.function.UnaryOperator;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.java.MapUtil;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.modifier.VisibilityModifier;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.proof.init.ContractPO;
import de.uka.ilkd.key.proof.init.DependencyContractPO;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProofOblInput;

/**
 * Standard implementation of the DependencyContract interface.
 */
public final class DependencyContractImpl implements DependencyContract {
    final String baseName;
    final String name;
    final KeYJavaType kjt;
    final IObserverFunction target;
    final KeYJavaType specifiedIn;
    final Map<LocationVariable,Term> originalPres;
    final Term originalMby;
    final Map<ProgramVariable,Term> originalDeps;
    final ProgramVariable originalSelfVar;
    final ImmutableList<ProgramVariable> originalParamVars;
    final Map<LocationVariable, ? extends ProgramVariable> originalAtPreVars;
    final Term globalDefs;
    final int id;


    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------

    DependencyContractImpl(String baseName,
            String name,
            KeYJavaType kjt,
            IObserverFunction target,
            KeYJavaType specifiedIn,
            Map<LocationVariable,Term> pres,
            Term mby,
            Map<ProgramVariable,Term> deps,
            ProgramVariable selfVar,
            ImmutableList<ProgramVariable> paramVars,
            Map<LocationVariable, ? extends ProgramVariable> atPreVars,
            Term globalDefs,
            int id) {
        assert baseName != null;
        assert kjt != null;
        assert target != null;
        assert pres != null;
        assert deps != null : "cannot create contract "+baseName+" for "+target+" when no specification is given";
        assert (selfVar == null) == target.isStatic();
        assert paramVars != null;
        // This cannot be done properly for multiple heaps without access to services:
        //assert paramVars.size() == target.arity() - (target.isStatic() ? 1 : 2);
        assert target.getStateCount() > 0;
        this.baseName = baseName;
        this.name = name != null
                ? name
                        : ContractFactory.generateContractName(baseName, kjt, target,
                                specifiedIn, id);
        this.kjt = kjt;
        this.target = target;
        this.specifiedIn = specifiedIn;
        this.originalPres = pres;
        this.originalMby = mby;
        this.originalDeps = deps;
        this.originalSelfVar = selfVar;
        this.originalParamVars = paramVars;
        this.originalAtPreVars = atPreVars;
        this.globalDefs = globalDefs;
        this.id = id;
    }


    @Deprecated
    DependencyContractImpl(String baseName,
            KeYJavaType kjt,
            IObserverFunction target,
            KeYJavaType specifiedIn,
            Map<LocationVariable,Term> pres,
            Term mby,
            Map<ProgramVariable,Term> deps,
            ProgramVariable selfVar,
            ImmutableList<ProgramVariable> paramVars,
            Map<LocationVariable,? extends ProgramVariable> atPreVars) {
        this(baseName,
                null,
                kjt,
                target,
                specifiedIn,
                pres,
                mby,
                deps,
                selfVar,
                paramVars,
                atPreVars,
                null,
                INVALID_ID);
    }

    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------

    @Override
    public DependencyContract map(UnaryOperator<Term> op, Services services) {
        Map<LocationVariable, Term> newPres = originalPres.entrySet().stream().collect(
                MapUtil.collector(Map.Entry::getKey, entry -> op.apply(entry.getValue())));
        Term newMby = op.apply(originalMby);
        Map<ProgramVariable, Term> newDeps = originalDeps.entrySet().stream().collect(
                MapUtil.collector(Map.Entry::getKey, entry -> op.apply(entry.getValue())));

        return new DependencyContractImpl(baseName, name, kjt, target, specifiedIn,
                newPres, newMby, newDeps,
                originalSelfVar, originalParamVars, originalAtPreVars,
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
    public Term getPre(LocationVariable heap,
            ProgramVariable selfVar,
            ImmutableList<ProgramVariable> paramVars,
            Map<LocationVariable, ? extends ProgramVariable> atPreVars,
            Services services) {
        assert (selfVar == null) == (originalSelfVar == null);
        assert paramVars != null;
        assert paramVars.size() == originalParamVars.size();
        assert services != null;
        Map<SVSubstitute, SVSubstitute> map = new LinkedHashMap<SVSubstitute, SVSubstitute>();
        if (originalSelfVar != null) {
            map.put(originalSelfVar, selfVar);
        }
        for(ProgramVariable originalParamVar : originalParamVars) {
            map.put(originalParamVar, paramVars.head());
            paramVars = paramVars.tail();
        }
        if(atPreVars != null && originalAtPreVars != null) {
            for(LocationVariable h : services.getTypeConverter().getHeapLDT().getAllHeaps()) {
                ProgramVariable originalAtPreVar = originalAtPreVars.get(h);
                if(atPreVars.get(h) != null && originalAtPreVar != null) {
                    map.put(services.getTermBuilder().var(originalAtPreVar), services.getTermBuilder().var(atPreVars.get(h)));
                }
            }
        }

        OpReplacer or = new OpReplacer(map, services.getTermFactory(), services.getProof());
        return or.replace(originalPres.get(heap));
    }

    @Override
    public Term getPre(List<LocationVariable> heapContext,
            ProgramVariable selfVar,
            ImmutableList<ProgramVariable> paramVars,
            Map<LocationVariable, ? extends ProgramVariable> atPreVars,
            Services services) {
        Term result = null;
        for(LocationVariable heap : heapContext) {
            final Term p = getPre(heap, selfVar, paramVars, atPreVars, services);
            if(result == null) {
                result = p;
            }else{
                result = services.getTermBuilder().and(result, p);
            }
        }
        return result;
    }


    @Override
    public Term getPre(LocationVariable heap,
            Term heapTerm,
            Term selfTerm,
            ImmutableList<Term> paramTerms,
            Map<LocationVariable,Term> atPres,
            Services services) {
        assert heapTerm != null;
        assert (selfTerm == null) == (originalSelfVar == null);
        assert paramTerms != null;
        assert paramTerms.size() == originalParamVars.size();
        assert services != null;
        Map<SVSubstitute, SVSubstitute> map = new LinkedHashMap<SVSubstitute, SVSubstitute>();
        map.put(services.getTermBuilder().var(heap), heapTerm);
        if (originalSelfVar != null) {
            map.put(services.getTermBuilder().var(originalSelfVar), selfTerm);
        }
        for(ProgramVariable originalParamVar : originalParamVars) {
            map.put(services.getTermBuilder().var(originalParamVar), paramTerms.head());
            paramTerms = paramTerms.tail();
        }
        if(atPres != null && originalAtPreVars != null) {
            for(LocationVariable h : services.getTypeConverter().getHeapLDT().getAllHeaps()) {
                ProgramVariable originalAtPreVar = originalAtPreVars.get(h);
                if(atPres.get(h) != null && originalAtPreVar != null) {
                    map.put(services.getTermBuilder().var(originalAtPreVar), atPres.get(h));
                }
            }
        }
        OpReplacer or = new OpReplacer(map, services.getTermFactory(), services.getProof());
        return or.replace(originalPres.get(heap));
    }


    @Override
    public Term getPre(List<LocationVariable> heapContext,
            Map<LocationVariable,Term> heapTerms,
            Term selfTerm,
            ImmutableList<Term> paramTerms,
            Map<LocationVariable,Term> atPres,
            Services services) {
        Term result = null;
        for(LocationVariable heap : heapContext) {
            final Term p = getPre(heap, heapTerms.get(heap), selfTerm, paramTerms, atPres, services);
            if(result == null) {
                result = p;
            }else{
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
    public Term getAssignable(LocationVariable heap) {
        throw new UnsupportedOperationException("Not applicable for dependency contracts.");
    }

    @Override
    public Term getAccessible(ProgramVariable heap) {
        return originalDeps.get(heap);
    }

    @Override
    public Term getMby() {
        return this.originalMby;
    }

    @Override
    public Term getMby(ProgramVariable selfVar,
            ImmutableList<ProgramVariable> paramVars,
            Services services) {
        assert hasMby();
        assert (selfVar == null) == (originalSelfVar == null);
        assert paramVars != null;
        assert paramVars.size() == originalParamVars.size();
        assert services != null;
        Map<SVSubstitute, SVSubstitute> map = new LinkedHashMap<SVSubstitute, SVSubstitute>();
        if (originalSelfVar != null) {
            map.put(originalSelfVar, selfVar);
        }
        for(ProgramVariable originalParamVar : originalParamVars) {
            map.put(originalParamVar, paramVars.head());
            paramVars = paramVars.tail();
        }
        OpReplacer or = new OpReplacer(map, services.getTermFactory(), services.getProof());
        return or.replace(originalMby);
    }


    @Override
    public Term getMby(Map<LocationVariable,Term> heapTerms,
            Term selfTerm,
            ImmutableList<Term> paramTerms,
            Map<LocationVariable,Term> atPres,
            Services services) {
        assert hasMby();
        assert heapTerms != null;
        assert (selfTerm == null) == (originalSelfVar == null);
        assert paramTerms != null;
        assert paramTerms.size() == originalParamVars.size();
        assert services != null;
        Map<SVSubstitute, SVSubstitute> map = new LinkedHashMap<SVSubstitute, SVSubstitute>();
        for(LocationVariable heap : heapTerms.keySet()) {
            map.put(services.getTermBuilder().var(heap), heapTerms.get(heap));
        }
        if (originalSelfVar != null) {
            map.put(services.getTermBuilder().var(originalSelfVar), selfTerm);
        }
        for(ProgramVariable originalParamVar : originalParamVars) {
            map.put(services.getTermBuilder().var(originalParamVar), paramTerms.head());
            paramTerms = paramTerms.tail();
        }
        if(atPres != null && originalAtPreVars != null) {
            for(LocationVariable h : services.getTypeConverter().getHeapLDT().getAllHeaps()) {
                ProgramVariable originalAtPreVar = originalAtPreVars.get(h);
                if(atPres.get(h) != null && originalAtPreVar != null) {
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
        String pres = "";
        for(LocationVariable h : originalPres.keySet()) {
            Term originalPre = originalPres.get(h);
            if(originalPre != null) {
                pres = pres + "<b>pre["+h+"]</b> "+LogicPrinter.escapeHTML(LogicPrinter.quickPrintTerm(originalPre, services),false)+"<br>";
            }
        }
        String deps = "";
        for(ProgramVariable h : originalDeps.keySet()) {
            if(h.name().toString().endsWith("AtPre") && target.getStateCount() == 1) {
                continue;
            }
            Term originalDep = originalDeps.get(h);
            if(originalDep != null) {
                deps = deps + "<b>dep["+h+"]</b> "+LogicPrinter.escapeHTML(LogicPrinter.quickPrintTerm(originalDep, services),false)+"<br>";
            }
        }
        final String mby = hasMby()
                ? LogicPrinter.quickPrintTerm(originalMby, services)
                        : null;

                if (includeHtmlMarkup) {
                    return "<html>"
                            + pres
                            + deps
                            + (mby != null
                            ? "<br><b>measured-by</b> " + LogicPrinter.escapeHTML(mby,
                                    false)
                                    : "")
                                    + "</html>";
                }
                else {
                    return "pre: "
                            + pres
                            + "\ndep: "
                            + deps
                            + (hasMby() ? "\nmeasured-by: " + mby : "");
                }
    }


    @Override
    public boolean toBeSaved() {
        return false; //because dependency contracts currently cannot be
        //specified directly in DL
    }


    @Override
    public String proofToString(Services services) {
        assert false;
        return null;
    }


    @Override
    public Term getDep(LocationVariable heap, boolean atPre,
            ProgramVariable selfVar,
            ImmutableList<ProgramVariable> paramVars,
            Map<LocationVariable,? extends ProgramVariable> atPreVars,
            Services services) {
        assert (selfVar == null) == (originalSelfVar == null);
        assert paramVars != null;
        assert paramVars.size() == originalParamVars.size();
        assert services != null;
        Map<SVSubstitute, SVSubstitute> map = new LinkedHashMap<SVSubstitute, SVSubstitute>();
        if (originalSelfVar != null) {
            map.put(originalSelfVar, selfVar);
        }
        for(ProgramVariable originalParamVar : originalParamVars) {
            map.put(originalParamVar, paramVars.head());
            paramVars = paramVars.tail();
        }
        if(atPreVars != null && originalAtPreVars != null) {
            for(LocationVariable h : services.getTypeConverter().getHeapLDT().getAllHeaps()) {
                ProgramVariable originalAtPreVar = originalAtPreVars.get(h);
                if(atPreVars.get(h) != null && originalAtPreVar != null) {
                    map.put(services.getTermBuilder().var(atPre ? h : originalAtPreVar), services.getTermBuilder().var(atPreVars.get(h)));
                }
            }
        }
        OpReplacer or = new OpReplacer(map, services.getTermFactory(), services.getProof());
        return or.replace(originalDeps.get(atPre ? originalAtPreVars.get(heap) : heap));
    }


    @Override
    public Term getDep(LocationVariable heap, boolean atPre,
            Term heapTerm,
            Term selfTerm,
            ImmutableList<Term> paramTerms,
            Map<LocationVariable, Term> atPres,
            Services services) {
        assert heapTerm != null;
        assert (selfTerm == null) == (originalSelfVar == null);
        assert paramTerms != null;
        assert paramTerms.size() == originalParamVars.size();
        assert services != null;
        Map<SVSubstitute, SVSubstitute> map = new LinkedHashMap<SVSubstitute, SVSubstitute>();
        map.put(services.getTermBuilder().var(heap), heapTerm);
        if (originalSelfVar != null) {
            map.put(services.getTermBuilder().var(originalSelfVar), selfTerm);
        }
        for(ProgramVariable originalParamVar : originalParamVars) {
            map.put(services.getTermBuilder().var(originalParamVar), paramTerms.head());
            paramTerms = paramTerms.tail();
        }
        if(atPres != null && originalAtPreVars != null) {
            for(LocationVariable h : services.getTypeConverter().getHeapLDT().getAllHeaps()) {
                ProgramVariable originalAtPreVar = originalAtPreVars.get(h);
                if(originalAtPreVar != null && atPres.get(h) != null) {
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
    public Term getGlobalDefs(LocationVariable heap, Term heapTerm,
            Term selfTerm, ImmutableList<Term> paramTerms, Services services) {
        assert false: "old clauses are not yet supported for dependency contracts";
        return null;
    }

    @Override
    public String toString() {
        return originalDeps.toString();
    }


    @Override
    public String getDisplayName() {
        return ContractFactory.generateDisplayName(baseName, kjt, target,
                specifiedIn, id);
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
    public final ProofOblInput createProofObl(InitConfig initConfig, Contract contract, boolean addSymbolicExecutionLabel) {
        if (addSymbolicExecutionLabel) {
           throw new IllegalStateException("Symbolic Execution API is not supported.");
        }
        else {
           return createProofObl(initConfig, contract);
        }
    }


    @Override
    public ProofOblInput createProofObl(InitConfig initConfig,
                                     Contract contract) {
	return new DependencyContractPO(initConfig,
	                                (DependencyContract)contract);
    }


    @Override
    public final ContractPO createProofObl(InitConfig initConfig) {
        return (ContractPO)createProofObl(initConfig, this);
    }


    @Override
    public ProofOblInput getProofObl(Services services) {
        return services.getSpecificationRepository().getPO(this);
    }


    @Override
    public DependencyContract setID(int newId) {
        return new DependencyContractImpl(baseName,
                null,
                kjt,
                target,
                specifiedIn,
                originalPres,
                originalMby,
                originalDeps,
                originalSelfVar,
                originalParamVars,
                originalAtPreVars,
                globalDefs,
                newId);
    }


    @Override
    public Contract setTarget(KeYJavaType newKJT,
            IObserverFunction newPM) {
        return new DependencyContractImpl(baseName,
                null,
                newKJT,
                newPM,
                specifiedIn,
                originalPres,
                originalMby,
                originalDeps,
                originalSelfVar,
                originalParamVars,
                originalAtPreVars,
                globalDefs,
                id);
    }


    @Override
    public String getTypeName() {
        return ContractFactory.generateContractTypeName(baseName, kjt, target,
                specifiedIn);
    }

    @Override
    public boolean hasSelfVar() {
        return originalSelfVar != null;
    }

    @Override
    public OriginalVariables getOrigVars() {
        Map<LocationVariable, ProgramVariable> atPreVars =
                new LinkedHashMap<LocationVariable, ProgramVariable>();
        if (originalAtPreVars != null) {
            for (LocationVariable h: originalAtPreVars.keySet()) {
                atPreVars.put(h, originalAtPreVars.get(h));
            }
        }
        return new OriginalVariables(originalSelfVar, null, null,
                                     atPreVars, originalParamVars);
    }
}

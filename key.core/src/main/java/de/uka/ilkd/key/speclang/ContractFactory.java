/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang;

import java.util.*;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.label.OriginTermLabel;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.speclang.jml.translation.JMLSpecFactory;
import de.uka.ilkd.key.speclang.jml.translation.ProgramVariableCollection;
import de.uka.ilkd.key.speclang.translation.SLTranslationException;
import de.uka.ilkd.key.util.InfFlowSpec;
import de.uka.ilkd.key.util.Triple;

import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;

import static de.uka.ilkd.key.logic.label.OriginTermLabel.*;

/**
 * Contracts should only be created through methods of this class
 *
 * @author bruns
 *
 */
public class ContractFactory {

    /**
     * The base name for symbolic execution contracts.
     */
    public static final String SYMB_EXEC_CONTRACT_BASENAME = "Symbolic Execution";
    /**
     * The base name for information flow contracts.
     */
    public static final String INFORMATION_FLOW_CONTRACT_BASENAME = "Non-interference contract";

    private static final String INVALID_ID = "INVALID_ID";
    private static final String UNKNOWN_CONTRACT_IMPLEMENTATION = "unknown contract implementation";
    private static final String CONTRACT_COMBINATION_MARKER = "#";
    private final Services services;
    private final TermBuilder tb;

    /**
     * Creates a new contract factory.
     *
     * @param services the services object
     */
    public ContractFactory(Services services) {
        assert services != null;
        this.services = services;
        this.tb = services.getTermBuilder();
    }

    // PUBLIC INTERFACE

    /**
     * Returns another contract like this one, except that the passed term has been added as a
     * postcondition (regardless of termination case).
     *
     * @param old the old contract
     * @param addedPost the post condition to be added
     * @param selfVar the used self variable
     * @param resultVar the used result variable
     * @param excVar the used exception variable
     * @param paramVars the used program variables
     * @param atPreVars the used pre-heap variables
     * @return the resulting contract
     */
    public FunctionalOperationContract addPost(FunctionalOperationContract old, Term addedPost,
            ProgramVariable selfVar, ProgramVariable resultVar, ProgramVariable excVar,
            ImmutableList<ProgramVariable> paramVars,
            Map<LocationVariable, LocationVariable> atPreVars) {
        assert old instanceof FunctionalOperationContractImpl : UNKNOWN_CONTRACT_IMPLEMENTATION;
        FunctionalOperationContractImpl foci = (FunctionalOperationContractImpl) old;
        addedPost = replaceVariables(addedPost, selfVar, resultVar, excVar, paramVars, atPreVars,
            foci.originalSelfVar, foci.originalResultVar, foci.originalExcVar,
            foci.originalParamVars, foci.originalAtPreVars);

        Map<LocationVariable, Term> newPosts = new LinkedHashMap<>(10);
        for (LocationVariable h : foci.originalPosts.keySet()) {
            if (h == services.getTypeConverter().getHeapLDT().getHeap()) {
                newPosts.put(h, tb.andSC(foci.originalPosts.get(h), addedPost));
            } else {
                newPosts.put(h, foci.originalPosts.get(h));
            }
        }

        // create new contract
        return new FunctionalOperationContractImpl(foci.baseName, foci.name, foci.kjt, foci.pm,
            foci.specifiedIn, foci.modality, foci.originalPres, foci.originalFreePres,
            foci.originalMby, newPosts, foci.originalFreePosts, foci.originalAxioms,
            foci.originalMods, foci.originalFreeMods, foci.originalDeps, foci.hasRealModifiesClause,
            foci.hasRealFreeModifiesClause, foci.originalSelfVar, foci.originalParamVars,
            foci.originalResultVar, foci.originalExcVar, foci.originalAtPreVars, foci.globalDefs,
            foci.id, foci.toBeSaved, foci.transaction, services);
    }

    /**
     * Add the specification contained in InitiallyClause as a postcondition.
     *
     * @param old the old contract
     * @param ini the initially clause to be added
     * @return the resulting contract
     */
    public FunctionalOperationContract addPost(FunctionalOperationContract old,
            InitiallyClause ini) {
        final ProgramVariable selfVar = tb.selfVar(ini.getKJT(), true);
        return addPost(old, ini.getClause(selfVar, services), null, null, null, null, null);
    }

    /**
     * Returns another contract like this one, except that the passed term has been added as a
     * precondition.
     *
     * @param old the old contract
     * @param addedPre precondition to be added
     * @param selfVar used self variable
     * @param paramVars used program variables
     * @param atPreVars used pre-heap variables
     * @return the resulting contract
     */
    public FunctionalOperationContract addPre(FunctionalOperationContract old, Term addedPre,
            ProgramVariable selfVar, ImmutableList<ProgramVariable> paramVars,
            Map<LocationVariable, LocationVariable> atPreVars) {
        assert old instanceof FunctionalOperationContractImpl : UNKNOWN_CONTRACT_IMPLEMENTATION;
        FunctionalOperationContractImpl foci = (FunctionalOperationContractImpl) old;
        addedPre = replaceVariables(addedPre, selfVar, paramVars, atPreVars, foci.originalSelfVar,
            foci.originalParamVars, foci.originalAtPreVars);

        Map<LocationVariable, Term> newPres = new LinkedHashMap<>(10);
        for (LocationVariable h : foci.originalPres.keySet()) {
            if (h == services.getTypeConverter().getHeapLDT().getHeap()) {
                newPres.put(h, tb.and(foci.originalPres.get(h), addedPre));
            } else {
                newPres.put(h, foci.originalPres.get(h));
            }
        }

        // create new contract
        return new FunctionalOperationContractImpl(foci.baseName, foci.name, foci.kjt, foci.pm,
            foci.specifiedIn, foci.modality, newPres, foci.originalFreePres, foci.originalMby,
            foci.originalPosts, foci.originalFreePosts, foci.originalAxioms, foci.originalMods,
            foci.originalFreeMods, foci.originalDeps, foci.hasRealModifiesClause,
            foci.hasRealFreeModifiesClause, foci.originalSelfVar, foci.originalParamVars,
            foci.originalResultVar, foci.originalExcVar, foci.originalAtPreVars, foci.globalDefs,
            foci.id, foci.toBeSaved,
            foci.originalMods.get(services.getTypeConverter().getHeapLDT().getSavedHeap()) != null,
            services);
    }

    /**
     * Add global variable definitions (aka. old clause) to the contract.
     *
     * @param opc the functional method contract
     * @param globalDefs the global variable definitions
     * @return the resulting method contract
     */
    public FunctionalOperationContract addGlobalDefs(FunctionalOperationContract opc,
            Term globalDefs) {
        assert opc instanceof FunctionalOperationContractImpl : UNKNOWN_CONTRACT_IMPLEMENTATION;
        FunctionalOperationContractImpl foci = (FunctionalOperationContractImpl) opc;
        return new FunctionalOperationContractImpl(foci.baseName, foci.name, foci.kjt, foci.pm,
            foci.specifiedIn, foci.modality, foci.originalPres, foci.originalFreePres,
            foci.originalMby, foci.originalPosts, foci.originalFreePosts, foci.originalAxioms,
            foci.originalMods, foci.originalFreeMods, foci.originalDeps,
            foci.hasRealModifiesClause, foci.hasRealFreeModifiesClause, foci.originalSelfVar,
            foci.originalParamVars, foci.originalResultVar, foci.originalExcVar,
            foci.originalAtPreVars, globalDefs, foci.id, foci.toBeSaved, foci.transaction,
            services);
    }

    public DependencyContract dep(KeYJavaType containerType, IObserverFunction pm,
            KeYJavaType specifiedIn, Map<LocationVariable, Term> requires, Term measuredBy,
            Map<ProgramVariable, Term> accessibles, ProgramVariable selfVar,
            ImmutableList<ProgramVariable> paramVars,
            Map<LocationVariable, ? extends ProgramVariable> atPreVars, Term globalDefs) {
        assert (selfVar == null) == pm.isStatic();
        return dep("JML accessible clause", containerType, pm, specifiedIn, requires, measuredBy,
            accessibles, selfVar, paramVars, atPreVars, globalDefs);
    }

    public DependencyContract dep(KeYJavaType kjt, LocationVariable targetHeap,
            Triple<IObserverFunction, Term, Term> dep, ProgramVariable selfVar) {
        final ImmutableList<ProgramVariable> paramVars = tb.paramVars(dep.first, false);
        assert (selfVar == null) == dep.first.isStatic();
        Map<LocationVariable, Term> pres = new LinkedHashMap<>();
        pres.put(services.getTypeConverter().getHeapLDT().getHeap(),
            selfVar == null ? tb.tt() : tb.inv(tb.var(selfVar)));
        Map<ProgramVariable, Term> accessibles = new LinkedHashMap<>();
        for (LocationVariable heap : HeapContext.getModHeaps(services, false)) {
            if (heap == targetHeap) {
                accessibles.put(heap, dep.second);
            } else {
                accessibles.put(heap, tb.allLocs());
            }
        }
        // TODO: insert static invariant??
        return dep(kjt, dep.first, dep.first.getContainerType(), pres, dep.third, accessibles,
            selfVar, paramVars, null, null);
    }

    public DependencyContract dep(String string, KeYJavaType containerType, IObserverFunction pm,
            KeYJavaType specifiedIn, Map<LocationVariable, Term> requires, Term measuredBy,
            Map<ProgramVariable, Term> accessibles, ProgramVariable selfVar,
            ImmutableList<ProgramVariable> paramVars,
            Map<LocationVariable, ? extends ProgramVariable> atPreVars, Term globalDefs) {
        assert (selfVar == null) == pm.isStatic();
        return new DependencyContractImpl(string, null, containerType, pm, specifiedIn, requires,
            measuredBy, accessibles, selfVar, paramVars, atPreVars, globalDefs,
            Contract.INVALID_ID);
    }

    public InformationFlowContract createInformationFlowContract(KeYJavaType forClass,
            IProgramMethod pm, KeYJavaType specifiedIn, Modality modality, Term requires,
            Term requiresFree, Term measuredBy, Term modifies, boolean hasMod,
            ProgramVariableCollection progVars, Term accessible,
            ImmutableList<InfFlowSpec> infFlowSpecs, boolean toBeSaved) {
        final LocationVariable baseHeap = services.getTypeConverter().getHeapLDT().getHeap();
        final Term atPre = tb.var(progVars.atPreVars.get(baseHeap));
        final Term self = progVars.selfVar != null ? tb.var(progVars.selfVar) : null;
        final ImmutableList<Term> params = tb.var(progVars.paramVars);
        final Term result = progVars.resultVar != null ? tb.var(progVars.resultVar) : null;
        final Term exc = progVars.excVar != null ? tb.var(progVars.excVar) : null;
        return new InformationFlowContractImpl(INFORMATION_FLOW_CONTRACT_BASENAME, forClass, pm,
            specifiedIn, modality, requires, requiresFree, measuredBy, modifies, hasMod, self,
            params, result, exc, atPre, accessible, infFlowSpecs, toBeSaved);
    }

    @Override
    public boolean equals(Object o) {
        if (o instanceof ContractFactory) {
            return Objects.equals(services, ((ContractFactory) o).services);
        } else {
            return false;
        }
    }

    /**
     * Create a new {@link FunctionalBlockContract} from an existing {@link BlockContract}.
     *
     * @param blockContract the {@link BlockContract}.
     * @return a new {@link FunctionalBlockContract}.
     */
    public FunctionalBlockContract funcBlock(BlockContract blockContract) {
        return new FunctionalBlockContract(blockContract);
    }

    /**
     * Create a new {@link FunctionalLoopContract} from an existing {@link LoopContract}.
     *
     * @param loopContract the {@link LoopContract}.
     * @return a new {@link FunctionalLoopContract}.
     */
    public FunctionalLoopContract funcLoop(LoopContract loopContract) {
        return new FunctionalLoopContract(loopContract);
    }

    /**
     * Create a new {@link FunctionalOperationContract} from an existing {@link IProgramMethod} and
     * {@link InitiallyClause}.
     *
     * @param pm the {@link IProgramMethod}.
     * @param ini the {@link InitiallyClause}.
     * @return a new {@link FunctionalOperationContract}.
     * @throws SLTranslationException in case translating the initially clause fails.
     */
    public FunctionalOperationContract func(IProgramMethod pm, InitiallyClause ini)
            throws SLTranslationException {
        return new JMLSpecFactory(services).initiallyClauseToContract(ini, pm);
    }

    /**
     * Creates a new functional operation contract.
     *
     * @param baseName base name of the contract (does not have to be unique)
     * @param kjt the KeYJavaType of the class
     * @param pm the IProgramMethod to which the contract belongs
     * @param modality the modality of the contract
     * @param pres the precondition of the contract
     * @param freePres the free/unchecked precondition of the contract
     * @param mby the measured_by clause of the contract
     * @param posts the postcondition of the contract
     * @param freePosts the free/unchecked postcondition of the contract
     * @param axioms the class axioms of the method
     * @param mods the modifies clause of the contract
     * @param freeMods the free modifies clause of the contract
     * @param accs the dependency clause of the contract
     * @param hasMod whether the contract has a modifies set
     * @param hasFreeMod whether the contract has a free modifies set
     * @param selfVar the self variable
     * @param paramVars the parameter variables
     * @param resultVar the exception variable
     * @param excVar the result variable
     * @param atPreVars a map of all pre-heap variables
     * @param toBeSaved TODO
     * @return the resulting functional operation contract
     */
    public FunctionalOperationContract func(String baseName, KeYJavaType kjt, IProgramMethod pm,
            Modality modality, Map<LocationVariable, Term> pres,
            Map<LocationVariable, Term> freePres, Term mby, Map<LocationVariable, Term> posts,
            Map<LocationVariable, Term> freePosts, Map<LocationVariable, Term> axioms,
            Map<LocationVariable, Term> mods, Map<LocationVariable, Term> freeMods,
            Map<ProgramVariable, Term> accs,
            Map<LocationVariable, Boolean> hasMod, Map<LocationVariable, Boolean> hasFreeMod,
            ProgramVariable selfVar,
            ImmutableList<ProgramVariable> paramVars, ProgramVariable resultVar,
            ProgramVariable excVar, Map<LocationVariable, LocationVariable> atPreVars,
            boolean toBeSaved) {
        return new FunctionalOperationContractImpl(baseName, null, kjt, pm, pm.getContainerType(),
            modality, pres, freePres, mby, posts, freePosts, axioms, mods, freeMods, accs, hasMod,
            hasFreeMod, selfVar, paramVars, resultVar, excVar, atPreVars, null, Contract.INVALID_ID,
            toBeSaved,
            mods.get(services.getTypeConverter().getHeapLDT().getSavedHeap()) != null, services);
    }

    /**
     * Creates a new functional operation contract.
     *
     * @param baseName base name of the contract (does not have to be unique)
     * @param pm the IProgramMethod to which the contract belongs
     * @param terminates a boolean determining whether we also prove termination
     * @param pres the precondition of the contract
     * @param freePres the free/unchecked precondition of the contract
     * @param mby the measured_by clause of the contract
     * @param posts the postcondition of the contract
     * @param freePosts the free/unchecked postcondition of the contract
     * @param axioms the class axioms of the method
     * @param mods the modifies clause of the contract
     * @param freeMods the free modifies clause of the contract
     * @param accessibles the dependency clause of the contract
     * @param hasMod whether the contract has a modifies set
     * @param hasFreeMod whether the contract has a modifies set
     * @param pv a collection of the program variables
     * @return the resulting functional operation contract
     */
    public FunctionalOperationContract func(String baseName, IProgramMethod pm, boolean terminates,
            Map<LocationVariable, Term> pres, Map<LocationVariable, Term> freePres, Term mby,
            Map<LocationVariable, Term> posts, Map<LocationVariable, Term> freePosts,
            Map<LocationVariable, Term> axioms, Map<LocationVariable, Term> mods,
            Map<LocationVariable, Term> freeMods, Map<ProgramVariable, Term> accessibles,
            Map<LocationVariable, Boolean> hasMod, Map<LocationVariable, Boolean> hasFreeMod,
            ProgramVariableCollection pv) {
        return func(baseName, pm, terminates ? Modality.DIA : Modality.BOX, pres, freePres, mby,
            posts, freePosts, axioms, mods, freeMods, accessibles, hasMod, hasFreeMod, pv, false,
            mods.get(services.getTypeConverter().getHeapLDT().getSavedHeap()) != null);
    }

    /**
     * Creates a new functional operation contract.
     *
     * @param baseName base name of the contract (does not have to be unique)
     * @param pm the IProgramMethod to which the contract belongs
     * @param modality the modality of the contract
     * @param pres the precondition of the contract
     * @param freePres the free/unchecked precondition of the contract
     * @param mby the measured_by clause of the contract
     * @param posts the postcondition of the contract
     * @param freePosts the free/unchecked postcondition of the contract
     * @param axioms the class axioms of the method
     * @param mods the modifies clause of the contract
     * @param freeMods the free modifies clause of the contract
     * @param accessibles the dependency clause of the contract
     * @param hasMod whether the contract has a modifies set
     * @param hasFreeMod whether the contract has a modifies set
     * @param progVars the program variables
     * @param toBeSaved TODO
     * @param transaction TODO
     * @return the resulting functional operation contract
     */
    public FunctionalOperationContract func(String baseName, IProgramMethod pm, Modality modality,
            Map<LocationVariable, Term> pres, Map<LocationVariable, Term> freePres, Term mby,
            Map<LocationVariable, Term> posts, Map<LocationVariable, Term> freePosts,
            Map<LocationVariable, Term> axioms, Map<LocationVariable, Term> mods,
            Map<LocationVariable, Term> freeMods, Map<ProgramVariable, Term> accessibles,
            Map<LocationVariable, Boolean> hasMod, Map<LocationVariable, Boolean> hasFreeMod,
            ProgramVariableCollection progVars, boolean toBeSaved, boolean transaction) {
        return new FunctionalOperationContractImpl(baseName, null, pm.getContainerType(), pm,
            pm.getContainerType(), modality, pres, freePres, mby, posts, freePosts, axioms, mods,
            freeMods, accessibles, hasMod, hasFreeMod, progVars.selfVar, progVars.paramVars,
            progVars.resultVar, progVars.excVar, progVars.atPreVars, null, Contract.INVALID_ID,
            toBeSaved, transaction, services);
    }

    private static Modality combineModalities(Modality moda, Modality otherModality) {
        if (moda != otherModality) {
            // TODO are there other modalities to appear in contracts?
            // I know that this is extremely ugly, but I don't know how to combine other kinds
            // of modalities.
            if (moda == Modality.BOX) {
                assert otherModality == Modality.DIA
                        : "unknown modality " + otherModality + " in contract";
                // do nothing
            } else {
                assert moda == Modality.DIA : "unknown modality " + moda + " in contract";
                moda = Modality.BOX;
            }
        }
        return moda;
    }

    private static Term combineMeasuredBy(Term mby, Term otherMby, LocationVariable h,
            Term otherPre, Services services) {
        final TermBuilder tb = services.getTermBuilder();
        if (h == services.getTypeConverter().getHeapLDT().getHeap()) {
            // bugfix (MU)
            // if the first or the other contract do not have a
            // measured-by-clause, assume no clause at all
            if (mby == null || otherMby == null) {
                if (mby != null) {
                    mby = tb.ife(otherPre, mby, tb.zero());
                } else if (otherMby != null) {
                    mby = tb.ife(otherPre, otherMby, tb.zero());
                } else {
                    mby = null;
                }
            } else {
                mby = tb.ife(otherPre, otherMby, mby);
            }
        }
        return mby;
    }

    private static void combineModifies(FunctionalOperationContractImpl t,
            Map<LocationVariable, Boolean> hasMod, Map<LocationVariable, Term> mods,
            Map<LocationVariable, Term> uniformMod, FunctionalOperationContract other,
            LocationVariable h, Term otherPre, Services services) {
        final TermBuilder tb = services.getTermBuilder();
        if (hasMod.get(h) || t.hasModifiesClause(h) || other.hasModifiesClause(h)) {
            hasMod.put(h, true);
            Term m1 = mods.get(h);
            Term m2 = other.getMod(h, t.originalSelfVar, t.originalParamVars, services);
            if (m1 != null || m2 != null) {
                Term nm;
                if (m1 == null) {
                    nm = m2;
                } else if (m2 == null) {
                    nm = m1;
                } else {
                    nm = tb.intersect(m1, tb.ife(otherPre, m2, tb.allLocs()));

                    // check if the other mod is the same as the one in the uniform store.
                    // To obtain meaningful results, check for equality ignoring all term labels!
                    if (uniformMod.containsKey(h)) {
                        if (!uniformMod.get(h).equalsModTermLabels(m2)) {
                            uniformMod.remove(h);
                        } else {
                            // merge term labels (in particular origin labels) of both modifies
                            // terms
                            uniformMod.put(h, mergeTermLabels(uniformMod.get(h), m2, tb));
                        }
                    }
                }
                mods.put(h, nm);
            }
        }
    }

    /**
     * Merges the labels of the given terms, such that the resulting term contains the labels of the
     * input terms. An exception of this are origin labels: These are combined into a single one
     * containing both origins.
     */
    private static Term mergeTermLabels(Term uniformMod, Term otherMod, TermBuilder tb) {
        List<TermLabel> labels = uniformMod.getLabels().toList();
        List<TermLabel> newLabels = new ArrayList<>(labels);
        for (TermLabel ol : otherMod.getLabels()) {
            if (!labels.contains(ol)) {
                // origin labels need to be handled specially to correctly merge their origins
                if (ol instanceof OriginTermLabel) {
                    // find current uniform origin and merge it with other origin
                    OriginTermLabel uol = null;
                    for (TermLabel l : labels) {
                        if (l instanceof OriginTermLabel) {
                            // found origin label -> merge origins
                            Origin o1 = ((OriginTermLabel) ol).getOrigin();
                            Origin o2 = ((OriginTermLabel) l).getOrigin();
                            Set<Origin> origins = new HashSet<>();
                            origins.add(o1);
                            origins.add(o2);
                            uol = new OriginTermLabel(origins);
                            newLabels.add(uol);
                            break;
                        }
                    }
                    // if uniformMod has no origin, use other origin
                    if (uol == null) {
                        newLabels.add(ol);
                    }
                } else {
                    // copy all non-origin labels
                    newLabels.add(ol);
                }
            }
        }
        // update (overwrite) the labels of the uniform mod with the found ones
        return tb.label(uniformMod, new ImmutableArray<>(newLabels));
    }

    private static Map<ProgramVariable, Term> joinDependencies(FunctionalOperationContractImpl t,
            Map<ProgramVariable, Term> deps, FunctionalOperationContract other, Services services) {
        final TermBuilder tb = services.getTermBuilder();
        for (LocationVariable h : services.getTypeConverter().getHeapLDT().getAllHeaps()) {
            Term a1 = deps.get(h);
            Term a2 = other.getDep(h, false, t.originalSelfVar, t.originalParamVars,
                t.originalAtPreVars, services);
            if (a1 != null || a2 != null) {
                Term na = null;
                if (a1 == null) {
                    na = a2;
                } else if (a2 == null) {
                    na = a1;
                } else {
                    na = tb.union(a1, a2);
                }
                deps.put(h, na);
            }
            boolean preHeap = t.originalAtPreVars.get(h) != null;
            if (preHeap) {
                LocationVariable hPre = t.originalAtPreVars.get(h);
                Term a1Pre = deps.get(hPre);
                Term a2Pre = other.getDep(hPre, true, t.originalSelfVar, t.originalParamVars,
                    t.originalAtPreVars, services);
                if (a1Pre != null || a2Pre != null) {
                    Term naPre = null;
                    if (a1Pre == null) {
                        naPre = a2Pre;
                    } else if (a2Pre == null) {
                        naPre = a1Pre;
                    } else {
                        naPre = tb.union(a1Pre, a2Pre);
                    }
                    deps.put(hPre, naPre);
                }
            }
        }
        return deps;
    }


    /**
     * Join with other contracts.
     *
     * @param name name of the contract union
     * @param t the first passed contract
     * @param others the other passed contracts
     * @param pres the first contract's precondition
     * @param mby the first contract's measuredBy term
     * @param hasMod whether the first contract has a modifies clause
     * @param hasFreeMod whether the first contract has a free modifies clause
     * @param posts the first contract's postcondition
     * @param freePosts the first contract's free postconditions
     * @param axioms the first contract's axioms
     * @param mods the first contract's modifies clause
     * @param freeMods the first contract's free modifies clause
     * @param deps the first contract's dependency clause
     * @param moda the first contract's modality
     * @return the joined contract
     */
    private FunctionalOperationContract joinWithOtherContracts(final String name,
            FunctionalOperationContractImpl t, FunctionalOperationContract[] others,
            Map<LocationVariable, Term> pres, Term mby,
            Map<LocationVariable, Boolean> hasMod,
            Map<LocationVariable, Boolean> hasFreeMod,
            Map<LocationVariable, Term> uniformMod,
            Map<LocationVariable, Term> uniformFreeMod,
            Map<LocationVariable, Term> posts,
            Map<LocationVariable, Term> freePosts,
            Map<LocationVariable, Term> axioms,
            Map<LocationVariable, Term> mods,
            Map<LocationVariable, Term> freeMods,
            Map<ProgramVariable, Term> deps, Modality moda) {
        for (FunctionalOperationContract other : others) {
            moda = combineModalities(moda, other.getModality());
            Term otherMby =
                other.hasMby() ? other.getMby(t.originalSelfVar, t.originalParamVars, services)
                        : null;
            for (LocationVariable h : services.getTypeConverter().getHeapLDT().getAllHeaps()) {
                Term otherPre = other.getPre(h, t.originalSelfVar, t.originalParamVars,
                    t.originalAtPreVars, services);
                Term otherPost = other.getPost(h, t.originalSelfVar, t.originalParamVars,
                    t.originalResultVar, t.originalExcVar, t.originalAtPreVars, services);
                Term otherFreePost = other.getFreePost(h, t.originalSelfVar, t.originalParamVars,
                    t.originalResultVar, t.originalExcVar, t.originalAtPreVars, services);
                Term otherAxiom = other.getRepresentsAxiom(h, t.originalSelfVar,
                    t.originalParamVars, t.originalResultVar, t.originalAtPreVars, services);
                mby = combineMeasuredBy(mby, otherMby, h, otherPre, services);

                // the modifies clause must be computed before the preconditions
                combineModifies(t, hasMod, mods, uniformMod, other, h, otherPre, services);
                combineModifies(t, hasFreeMod, freeMods, uniformFreeMod, other, h, otherPre,
                    services);

                if (otherPre != null) {
                    pres.put(h, pres.get(h) == null ? otherPre : tb.or(pres.get(h), otherPre));
                }
                if (otherPost != null) {
                    final Term oPost = tb.imp(atPreify(otherPre, t.originalAtPreVars), otherPost);
                    posts.put(h, posts.get(h) == null ? oPost : tb.and(posts.get(h), oPost));
                }
                if (otherFreePost != null) {
                    final Term oFreePost =
                        tb.imp(atPreify(otherPre, t.originalAtPreVars), otherFreePost);
                    freePosts.put(h,
                        freePosts.get(h) == null ? oFreePost : tb.and(freePosts.get(h), oFreePost));
                }
                if (otherAxiom != null) {
                    final Term oAxiom = tb.imp(atPreify(otherPre, t.originalAtPreVars), otherAxiom);
                    axioms.put(h, axioms.get(h) == null ? oAxiom : tb.and(axioms.get(h), oAxiom));
                }
            }
            deps = joinDependencies(t, deps, other, services);
        }

        /*
         * If there is a uniform mod clause (i.e., the same for all joined contracts), then use that
         * instead of the disjunction of if-then-else expressions. (Related to an older fix by
         * Daniel Grahl for MT-1557.)
         */
        for (LocationVariable h : services.getTypeConverter().getHeapLDT().getAllHeaps()) {
            if (uniformMod.containsKey(h)) {
                mods.put(h, uniformMod.get(h));
            }
            if (uniformFreeMod.containsKey(h)) {
                freeMods.put(h, uniformFreeMod.get(h));
            }
        }

        /*
         * (*) free preconditions are not joined because no sensible joining operator suggests
         * itself. This is no problem, however, since combined contracts are only used for contract
         * application and free preconditions are not used there. 2015, mu
         */
        return new FunctionalOperationContractImpl(INVALID_ID, name, t.kjt, t.pm, t.specifiedIn,
            moda, pres, new LinkedHashMap<>(), // (*)
            mby, posts, freePosts, axioms, mods, freeMods, deps, hasMod, hasFreeMod,
            t.originalSelfVar, t.originalParamVars, t.originalResultVar, t.originalExcVar,
            t.originalAtPreVars, t.globalDefs, Contract.INVALID_ID, t.toBeSaved, t.transaction,
            services);
    }

    /**
     * Returns the union of the passed contracts. Probably you want to use
     * SpecificationRepository.combineContracts() instead, which additionally takes care that the
     * combined contract can be loaded later. The resulting contract has id "INVALID_ID".
     *
     * @param name name of the contract union
     * @param t the first contract
     * @param others the other contracts
     * @return the joined contract
     */
    private FunctionalOperationContract union(final String name, FunctionalOperationContractImpl t,
            FunctionalOperationContract[] others) {
        // MU: Bugfix #1489
        // Do not modify the data stores in t but make new copies
        Map<LocationVariable, Term> mods = new LinkedHashMap<>(t.originalMods);
        Map<LocationVariable, Term> freeMods = new LinkedHashMap<>(t.originalFreeMods);
        Map<ProgramVariable, Term> deps = new LinkedHashMap<>(t.originalDeps);

        // keep this to check if every contract has the same mod
        // then no if-then-else cascades are needed.
        Map<LocationVariable, Term> uniformMod = new LinkedHashMap<>();
        Map<LocationVariable, Term> uniformFreeMod = new LinkedHashMap<>();

        // collect information
        Map<LocationVariable, Term> pres = new LinkedHashMap<>(t.originalPres.size());
        for (LocationVariable h : t.originalPres.keySet()) {
            pres.put(h, t.originalPres.get(h));
        }
        Term mby = t.originalMby;
        Map<LocationVariable, Boolean> hasMod = new LinkedHashMap<>();
        Map<LocationVariable, Boolean> hasFreeMod = new LinkedHashMap<>();
        Map<LocationVariable, Term> posts = new LinkedHashMap<>(t.originalPosts.size());
        Map<LocationVariable, Term> freePosts = new LinkedHashMap<>(t.originalFreePosts.size());
        for (LocationVariable h : services.getTypeConverter().getHeapLDT().getAllHeaps()) {
            hasMod.put(h, false);
            hasFreeMod.put(h, false);
            Term oriPost = t.originalPosts.get(h);
            Term oriFreePost = t.originalFreePosts.get(h);
            if (oriPost != null) {
                posts.put(h, tb.imp(atPreify(t.originalPres.get(h), t.originalAtPreVars), oriPost));
            }
            if (oriFreePost != null) {
                freePosts.put(h,
                    tb.imp(atPreify(t.originalFreePres.get(h), t.originalAtPreVars), oriFreePost));
            }
            Term origMod = t.originalMods.get(h);
            if (origMod != null) {
                mods.put(h, tb.ife(t.originalPres.get(h), origMod, tb.allLocs()));
                uniformMod.put(h, origMod);
            }
            Term origFreeMod = t.originalFreeMods.get(h);
            if (origFreeMod != null) {
                freeMods.put(h, tb.ife(t.originalPres.get(h), origFreeMod, tb.allLocs()));
                uniformFreeMod.put(h, origFreeMod);
            }
        }

        Map<LocationVariable, Term> axioms = new LinkedHashMap<>();
        if (t.originalAxioms != null) { // TODO: what about the others?
            for (LocationVariable h : services.getTypeConverter().getHeapLDT().getAllHeaps()) {
                Term oriAxiom = t.originalAxioms.get(h);
                if (oriAxiom != null) {
                    axioms.put(h,
                        tb.imp(atPreify(t.originalPres.get(h), t.originalAtPreVars), oriAxiom));
                }
            }
        }
        Modality moda = t.modality;
        return joinWithOtherContracts(name, t, others, pres, mby,
            hasMod, hasFreeMod, uniformMod, uniformFreeMod,
            posts, freePosts, axioms, mods, freeMods, deps, moda);

    }

    /**
     * Returns the union of the passed contracts. Probably you want to use
     * SpecificationRepository.combineContracts() instead, which additionally takes care that the
     * combined contract can be loaded later. The resulting contract has id "INVALID_ID".
     *
     * @param t the first passed contract
     * @param others the remaining passed contracts
     * @return the union contract
     */
    private FunctionalOperationContract union(FunctionalOperationContractImpl t,
            FunctionalOperationContract[] others) {
        // determine names
        StringBuilder nameSB = new StringBuilder(t.getName());
        for (FunctionalOperationContract other : others) {
            nameSB.append(CONTRACT_COMBINATION_MARKER).append(other.getName());
        }
        final String name = nameSB.toString();

        for (FunctionalOperationContract contract : others) {
            assert contract.getTarget().equals(t.pm);
        }
        return union(name, t, others);
    }

    /**
     * Returns the union of the passed contracts. Probably you want to use
     * SpecificationRepository.combineContracts() instead, which additionally takes care that the
     * combined contract can be loaded later. The resulting contract has id "INVALID_ID".
     *
     * @param contracts the passed contracts
     * @return the union contract
     */
    public FunctionalOperationContract union(FunctionalOperationContract... contracts) {
        if (contracts.length == 0) {
            return null;
        }
        if (contracts.length == 1) {
            return contracts[0];
        }
        assert contracts[0] instanceof FunctionalOperationContractImpl
                : UNKNOWN_CONTRACT_IMPLEMENTATION;

        FunctionalOperationContractImpl t = (FunctionalOperationContractImpl) contracts[0];
        FunctionalOperationContract[] others = Arrays.copyOfRange(contracts, 1, contracts.length);
        assert others != null;
        return union(t, others);
    }

    // PRIVATE METHODS

    private static <T> void addToMap(T var, T originalVar, Map<T, T> map) {
        if (var != null) {
            map.put(var, originalVar);
        }
    }

    private Term atPreify(Term t, Map<LocationVariable, ? extends ProgramVariable> atPreVars) {
        final Map<Term, Term> map = new LinkedHashMap<>(atPreVars.size());
        for (LocationVariable h : atPreVars.keySet()) {
            if (atPreVars.get(h) != null) {
                map.put(tb.var(h), tb.var(atPreVars.get(h)));
            }
        }
        return new OpReplacer(map, services.getTermFactory(), services.getProof()).replace(t);
    }

    /** replace in original the variables used for self and parameters */
    private Term replaceVariables(Term original, ProgramVariable selfVar,
            ImmutableList<ProgramVariable> paramVars,
            Map<LocationVariable, LocationVariable> atPreVars, ProgramVariable originalSelfVar,
            ImmutableList<ProgramVariable> originalParamVars,
            Map<LocationVariable, LocationVariable> originalAtPreVars) {
        return replaceVariables(original, selfVar, null, null, paramVars, atPreVars,
            originalSelfVar, null, null, originalParamVars, originalAtPreVars);
    }

    /** replace in original the variables used for self, result, exception, heap, and parameters */
    private Term replaceVariables(Term original, ProgramVariable selfVar, ProgramVariable resultVar,
            ProgramVariable excVar, ImmutableList<ProgramVariable> paramVars,
            Map<LocationVariable, LocationVariable> atPreVars, ProgramVariable originalSelfVar,
            ProgramVariable originalResultVar, ProgramVariable originalExcVar,
            ImmutableList<ProgramVariable> originalParamVars,
            Map<LocationVariable, LocationVariable> originalAtPreVars) {
        Map<Operator, Operator> map = new LinkedHashMap<>();
        addToMap(selfVar, originalSelfVar, map);
        addToMap(resultVar, originalResultVar, map);
        addToMap(excVar, originalExcVar, map);
        for (LocationVariable h : originalAtPreVars.keySet()) {
            if (atPreVars != null && atPreVars.get(h) != null) {
                addToMap(atPreVars.get(h), originalAtPreVars.get(h), map);
            }
        }
        if (paramVars != null) {
            Iterator<ProgramVariable> it1 = paramVars.iterator();
            Iterator<ProgramVariable> it2 = originalParamVars.iterator();
            while (it1.hasNext()) {
                assert it2.hasNext();
                map.put(it1.next(), it2.next());
            }
        }
        OpReplacer or = new OpReplacer(map, services.getTermFactory(), services.getProof());
        original = or.replace(original);
        return original;
    }

    @Override
    public int hashCode() {
        return services == null ? 0 : services.hashCode();
    }

    public static String generateDisplayName(String baseName, KeYJavaType forClass,
            IObserverFunction target, KeYJavaType specifiedIn, int myId) {
        return baseName + " " + myId + (specifiedIn.equals(forClass) ? ""
                : " for " + specifiedIn.getJavaType().getFullName());
    }

    public static String generateContractName(String baseName, KeYJavaType forClass,
            IObserverFunction target, KeYJavaType specifiedIn, int myId) {
        return generateContractTypeName(baseName, forClass, target, specifiedIn) + "." + myId;
    }

    public static String generateContractTypeName(String baseName, KeYJavaType forClass,
            IObserverFunction target, KeYJavaType specifiedIn) {
        final String methodName = target.name().toString();
        final int startIndexShortName = methodName.indexOf("::") + 2;
        final String methodShortName = methodName.substring(startIndexShortName);
        return forClass.getJavaType().getFullName() + "[" + specifiedIn.getJavaType().getFullName()
            + "::" + methodShortName + "(" + concatenate(",", target.getParamTypes()) + ")" + "]"
            + "." + baseName;
    }

    private static String concatenate(String delim, ImmutableArray<KeYJavaType> elems) {
        StringBuilder b = new StringBuilder();
        for (int i = 0; i < elems.size(); i++) {
            b.append(elems.get(i).getFullName());
            if (i + 1 < elems.size()) {
                b.append(delim);
            }
        }
        return b.toString();
    }
}

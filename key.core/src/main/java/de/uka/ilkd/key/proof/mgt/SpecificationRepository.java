/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.mgt;

import java.net.URI;
import java.util.*;
import java.util.Map.Entry;
import java.util.function.UnaryOperator;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.ClassDeclaration;
import de.uka.ilkd.key.java.declaration.modifier.Private;
import de.uka.ilkd.key.java.declaration.modifier.VisibilityModifier;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.java.statement.MergePointStatement;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ContractPO;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.rule.RewriteTaclet;
import de.uka.ilkd.key.rule.RuleSet;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.tacletbuilder.RewriteTacletBuilder;
import de.uka.ilkd.key.rule.tacletbuilder.RewriteTacletGoalTemplate;
import de.uka.ilkd.key.speclang.*;
import de.uka.ilkd.key.speclang.jml.JMLInfoExtractor;
import de.uka.ilkd.key.speclang.jml.translation.ProgramVariableCollection;
import de.uka.ilkd.key.speclang.translation.SLTranslationException;
import de.uka.ilkd.key.util.MiscTools;
import de.uka.ilkd.key.util.Triple;

import org.key_project.logic.Name;
import org.key_project.logic.sort.Sort;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;
import org.key_project.util.collection.Pair;

import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Central storage for all specification elements, such as contracts, class axioms, and loop
 * invariants. Provides methods for adding such elements to the repository, and for retrieving them
 * afterwards.
 */
public final class SpecificationRepository {
    private static final Logger LOGGER = LoggerFactory.getLogger(SpecificationRepository.class);

    public static final String CONTRACT_COMBINATION_MARKER = "#";

    /**
     * @see #limitObs(IObserverFunction)
     * @see #unlimitObs(IObserverFunction)
     */
    public static final String LIMIT_SUFFIX = "$lmtd";


    private final ContractFactory cf;

    private final Map<Pair<KeYJavaType, IObserverFunction>, ImmutableSet<Contract>> contracts =
        new LinkedHashMap<>();
    private final Map<Pair<KeYJavaType, IProgramMethod>, ImmutableSet<FunctionalOperationContract>> operationContracts =
        new LinkedHashMap<>();
    private final Map<Pair<KeYJavaType, IObserverFunction>, ImmutableSet<WellDefinednessCheck>> wdChecks =
        new LinkedHashMap<>();
    private final Map<String, Contract> contractsByName = new LinkedHashMap<>();
    private final Map<KeYJavaType, ImmutableSet<IObserverFunction>> contractTargets =
        new LinkedHashMap<>();
    private final Map<KeYJavaType, ImmutableSet<ClassInvariant>> invs = new LinkedHashMap<>();
    private final Map<KeYJavaType, ImmutableSet<ClassAxiom>> axioms = new LinkedHashMap<>();
    private final Map<KeYJavaType, ImmutableSet<InitiallyClause>> initiallyClauses =
        new LinkedHashMap<>();
    private final Map<ProofOblInput, ImmutableSet<Proof>> proofs = new LinkedHashMap<>();
    private final Map<Pair<LoopStatement, Integer>, LoopSpecification> loopInvs =
        new LinkedHashMap<>();
    private final Map<Triple<StatementBlock, URI, Integer>, ImmutableSet<BlockContract>> blockContracts =
        new LinkedHashMap<>();
    private final Map<Triple<StatementBlock, URI, Integer>, ImmutableSet<LoopContract>> loopContracts =
        new LinkedHashMap<>();
    /**
     * A map which relates each loop statement its starting line number and set of loop contracts.
     */
    private final Map<Pair<LoopStatement, Integer>, ImmutableSet<LoopContract>> loopContractsOnLoops =
        new LinkedHashMap<>();
    private final Map<MergePointStatement, ImmutableSet<MergeContract>> mergeContracts =
        new LinkedHashMap<>();
    private final Map<IObserverFunction, IObserverFunction> unlimitedToLimited =
        new LinkedHashMap<>();
    private final Map<IObserverFunction, IObserverFunction> limitedToUnlimited =
        new LinkedHashMap<>();
    private final Map<IObserverFunction, ImmutableSet<Taclet>> unlimitedToLimitTaclets =
        new LinkedHashMap<>();

    /**
     * <p>
     * This {@link Map} is used to store the result of {@link #getClassAxioms(KeYJavaType)} to avoid
     * that {@link RepresentsAxiom} and {@link QueryAxiom} are instantiated multiple times.
     * </p>
     * <p>
     * It is strongly required that always the same instances are returned because
     * {@link Object#equals(Object)} and {@link Object#hashCode()} is not implemented in instances
     * of {@link ClassAxiom} and such the default reference check is done which off cause always
     * fails in case of different references.
     * </p>
     */
    private final Map<KeYJavaType, ImmutableSet<ClassAxiom>> allClassAxiomsCache =
        new LinkedHashMap<>();

    private final Services services;
    private final TermBuilder tb;

    private final Map<String, Integer> contractCounters =
        new de.uka.ilkd.key.util.LinkedHashMap<>();

    public SpecificationRepository(Services services) {
        this.services = services;
        this.tb = services.getTermBuilder();
        cf = new ContractFactory(services);
    }

    // -------------------------------------------------------------------------
    // internal methods
    // -------------------------------------------------------------------------

    private static String getUniqueNameForObserver(IObserverFunction obs) {
        var sb = new StringBuilder(obs.name().toString());

        if (obs.isStatic()) {
            sb.append("_static_");
        }

        for (KeYJavaType pType : obs.getParamTypes()) {
            sb.append(pType.getFullName());
        }

        return sb.toString();
    }

    private static Taclet getLimitedToUnlimitedTaclet(IObserverFunction limited,
            IObserverFunction unlimited, TermServices services) {
        final TermBuilder tb = services.getTermBuilder();
        assert limited.arity() == unlimited.arity();

        // create schema terms
        final Term[] subs = new Term[limited.arity()];
        for (int i = 0; i < subs.length; i++) {
            final SchemaVariable argSV = SchemaVariableFactory.createTermSV(new Name("t" + i),
                limited.argSort(i), false, false);
            subs[i] = tb.var(argSV);
        }
        final Term limitedTerm = tb.func(limited, subs);
        final Term unlimitedTerm = tb.func(unlimited, subs);

        // create taclet
        final RewriteTacletBuilder<RewriteTaclet> tacletBuilder = new RewriteTacletBuilder<>();
        tacletBuilder.setFind(limitedTerm);
        tacletBuilder.addTacletGoalTemplate(new RewriteTacletGoalTemplate(Sequent.EMPTY_SEQUENT,
            ImmutableSLList.nil(), unlimitedTerm));
        tacletBuilder.setName(
            MiscTools.toValidTacletName("unlimit " + getUniqueNameForObserver(unlimited)));
        return tacletBuilder.getTaclet();
    }

    private static Taclet getUnlimitedToLimitedTaclet(IObserverFunction limited,
            IObserverFunction unlimited, TermServices services) {
        assert limited.arity() == unlimited.arity();

        final TermBuilder tb = services.getTermBuilder();
        // create schema terms
        final Term[] subs = new Term[limited.arity()];
        for (int i = 0; i < subs.length; i++) {
            final SchemaVariable argSV = SchemaVariableFactory.createTermSV(new Name("t" + i),
                limited.argSort(i), false, false);
            subs[i] = tb.var(argSV);
        }
        final Term limitedTerm = tb.func(limited, subs);
        final Term unlimitedTerm = tb.func(unlimited, subs);

        // create taclet
        final RewriteTacletBuilder<RewriteTaclet> tacletBuilder = new RewriteTacletBuilder<>();
        tacletBuilder.setFind(tb.func(unlimited, subs));
        final SequentFormula cf = new SequentFormula(tb.equals(limitedTerm, unlimitedTerm));
        final Sequent addedSeq =
            Sequent.createAnteSequent(Semisequent.EMPTY_SEMISEQUENT.insertFirst(cf).semisequent());
        tacletBuilder.addTacletGoalTemplate(new RewriteTacletGoalTemplate(addedSeq,
            ImmutableSLList.nil(), tb.func(unlimited, subs)));
        tacletBuilder.setApplicationRestriction(RewriteTaclet.IN_SEQUENT_STATE);
        tacletBuilder.setName(
            MiscTools.toValidTacletName("limit " + getUniqueNameForObserver(unlimited)));
        tacletBuilder.addRuleSet(new RuleSet(new Name("limitObserver")));

        return tacletBuilder.getTaclet();
    }

    private static Modality.JavaModalityKind getMatchModalityKind(
            final Modality.JavaModalityKind kind) {
        if (kind.transaction()) {
            return kind == Modality.JavaModalityKind.DIA_TRANSACTION ? Modality.JavaModalityKind.DIA
                    : Modality.JavaModalityKind.BOX;
        } else {
            return kind;
        }
    }

    private IObserverFunction getCanonicalFormForKJT(IObserverFunction obs, KeYJavaType kjt) {
        assert obs != null;
        assert kjt != null;
        if (!(obs instanceof IProgramMethod pm) || obs.getContainerType().equals(kjt)) {
            return unlimitObs(obs);
        }
        if (pm.isConstructor()) {
            assert pm.getContainerType().equals(kjt);
            return pm;
        }

        // search through all locally available methods
        final String name = pm.getMethodDeclaration().getName();
        final int numParams = pm.getParameterDeclarationCount();
        final ImmutableList<IProgramMethod> candidatePMs =
            services.getJavaInfo().getAllProgramMethods(kjt);
        outer: for (IProgramMethod candidatePM : candidatePMs) {
            if (candidatePM.getMethodDeclaration().getName().equals(name)
                    && candidatePM.getParameterDeclarationCount() == numParams) {
                for (int i = 0; i < numParams; i++) {
                    if (!candidatePM.getParameterType(i).equals(pm.getParameterType(i))) {
                        continue outer;
                    }
                }
                return candidatePM;
            }
        }

        // not found (happens for private methods of superclasses)
        // -> search through superclasses
        for (KeYJavaType sup : services.getJavaInfo().getAllSupertypes(kjt).removeAll(kjt)) {
            final IProgramMethod result = (IProgramMethod) getCanonicalFormForKJT(obs, sup);
            if (result != null) {
                return result;
            }
        }

        // should not happen
        assert false : "Could not find method " + pm.getName() + " in type " + kjt;
        return null;
    }

    private ImmutableSet<Pair<KeYJavaType, IObserverFunction>> getOverridingMethods(KeYJavaType kjt,
            IProgramMethod pm) {
        ImmutableList<Pair<KeYJavaType, IObserverFunction>> result = ImmutableSLList.nil();

        // static methods and constructors are not overriden
        if (pm.isConstructor() || pm.isStatic()) {
            return DefaultImmutableSet.fromImmutableList(result);
        }

        assert kjt != null;
        final JavaInfo javaInfo = services.getJavaInfo();
        for (KeYJavaType sub : javaInfo.getAllSubtypes(kjt)) {
            assert sub != null;
            final IProgramMethod subPM = (IProgramMethod) getCanonicalFormForKJT(pm, sub);
            result = result.prepend(new Pair<>(sub, subPM));
        }

        return DefaultImmutableSet.fromImmutableList(result);
    }

    public ImmutableSet<Pair<KeYJavaType, IObserverFunction>> getOverridingTargets(KeYJavaType kjt,
            IObserverFunction target) {
        if (target instanceof IProgramMethod) {
            return getOverridingMethods(kjt, (IProgramMethod) target);
        } else {
            ImmutableSet<Pair<KeYJavaType, IObserverFunction>> result = DefaultImmutableSet.nil();
            for (KeYJavaType sub : services.getJavaInfo().getAllSubtypes(kjt)) {
                result = result.add(new Pair<>(sub, target));
            }
            return result;
        }
    }

    /**
     * <p>
     * Returns all known class invariants for the passed type.
     * </p>
     * <p>
     * This method is used by Visual DbC and has to be public.
     * </p>
     */
    public ImmutableSet<ClassInvariant> getClassInvariants(KeYJavaType kjt) {
        ImmutableSet<ClassInvariant> result = invs.get(kjt);
        return result == null ? DefaultImmutableSet.nil() : result;
    }

    /**
     * Returns the kjt for the outer class, if the passed kjt is a member class, and null otherwise.
     */
    private KeYJavaType getEnclosingKJT(KeYJavaType kjt) {
        // HACK, this should be easier
        if (kjt.getJavaType() instanceof ClassDeclaration) {

            final String name = kjt.getJavaType().getFullName();

            if (name.contains(".")) {
                final String enclosingName = name.substring(0, name.lastIndexOf('.'));
                return services.getJavaInfo().getTypeByName(enclosingName);
            } else {
                return null;
            }
        } else {
            return null;
        }
    }

    private ImmutableSet<ClassAxiom> getVisibleAxiomsOfOtherClasses(KeYJavaType visibleTo) {
        ImmutableSet<ClassAxiom> result = DefaultImmutableSet.nil();
        for (Map.Entry<KeYJavaType, ImmutableSet<ClassAxiom>> e : axioms.entrySet()) {
            if (e.getKey().equals(visibleTo)) {
                continue;
            }
            for (ClassAxiom ax : e.getValue()) {
                if (JavaInfo.isVisibleTo(ax, visibleTo)) {
                    result = result.add(ax);
                }
            }
        }
        return result;
    }

    private RepresentsAxiom getRepresentsAxiom(KeYJavaType kjt, ClassAxiom ax) {
        if (!(ax instanceof RepresentsAxiom) || axioms.get(kjt) == null) {
            return null;
        }
        RepresentsAxiom result = null;
        for (ClassAxiom ca : axioms.get(kjt)) {
            if (ca instanceof RepresentsAxiom && (ca.getTarget().equals(ax.getTarget()))) {
                assert result == null : "More than one represents clause for " + ax.getTarget();
                result = (RepresentsAxiom) ca;
            }
        }
        return result;
    }

    private Contract prepareContract(Contract contract) {
        // sanity check
        assert getCanonicalFormForKJT(contract.getTarget(), contract.getKJT())
                .equals(contract.getTarget());

        // set id
        Integer nextId = contractCounters.get(contract.getTypeName());
        if (nextId == null) {
            nextId = 0;
        }
        contract = contract.setID(nextId);
        contractCounters.put(contract.getTypeName(), nextId + 1);
        return contract;
    }

    private void registerContract(Contract contract) {
        final Pair<KeYJavaType, IObserverFunction> target =
            new Pair<>(contract.getKJT(), contract.getTarget());
        registerContract(contract, target);
    }

    private void registerContract(Contract contract,
            final ImmutableSet<Pair<KeYJavaType, IObserverFunction>> targets) {
        for (Pair<KeYJavaType, IObserverFunction> impl : targets) {
            registerContract(contract, impl);
        }
    }

    private void registerContract(Contract contract,
            Pair<KeYJavaType, IObserverFunction> targetPair) {
        LOGGER.trace("Contract registered {}", contract);
        if (!WellDefinednessCheck.isOn() && contract instanceof WellDefinednessCheck) {
            return;
        }
        final KeYJavaType targetKJT = targetPair.first;
        final IObserverFunction targetMethod = targetPair.second;
        contract = contract.setTarget(targetKJT, targetMethod);
        final String name = contract.getName();
        assert contractsByName.get(name) == null
                : "Tried to add a contract with a non-unique name: " + name;
        assert !name.contains(CONTRACT_COMBINATION_MARKER)
                : "Tried to add a contract with a name containing the" + " reserved character "
                    + CONTRACT_COMBINATION_MARKER + ": " + name;
        assert contract.id() != Contract.INVALID_ID : "Tried to add a contract with an invalid id!";
        contracts.put(targetPair, getContracts(targetKJT, targetMethod).add(contract));

        if (contract instanceof FunctionalOperationContract) {
            operationContracts.put(new Pair<>(targetKJT, (IProgramMethod) targetMethod),
                getOperationContracts(targetKJT, (IProgramMethod) targetMethod)
                        .add((FunctionalOperationContract) contract));
            // Create new well-definedness check
            final MethodWellDefinedness mwd =
                new MethodWellDefinedness((FunctionalOperationContract) contract, services);
            registerContract(mwd);
        } else if (contract instanceof DependencyContract && contract.getOrigVars().atPres.isEmpty()
                && targetMethod.getContainerType()
                        .equals(services.getJavaInfo().getJavaLangObject())) {
            // Create or extend a well-definedness check for a class invariant
            final Term deps =
                contract.getAccessible(services.getTypeConverter().getHeapLDT().getHeap());
            final Term mby = contract.getMby();
            final String invName = "JML model class invariant in " + targetKJT.getName();
            final ClassInvariant inv = new ClassInvariantImpl(invName, invName, targetKJT,
                contract.getVisibility(), tb.tt(), contract.getOrigVars().self);
            ClassWellDefinedness cwd =
                new ClassWellDefinedness(inv, targetMethod, deps, mby, services);
            final ImmutableSet<ClassWellDefinedness> cwds = getWdClassChecks(targetKJT);
            if (!cwds.isEmpty()) {
                assert cwds.size() == 1;
                final ClassWellDefinedness oldCwd = cwds.iterator().next();
                unregisterContract(oldCwd);
                oldCwd.addInv(cwd.getInvariant().getInv(oldCwd.getOrigVars().self, services));
                cwd = oldCwd.combine(cwd, services);
            }
            registerContract(cwd);
        } else if (contract instanceof DependencyContract
                && contract.getOrigVars().atPres.isEmpty()) {
            // Create or extend a well-definedness check for a model field
            MethodWellDefinedness mwd =
                new MethodWellDefinedness((DependencyContract) contract, services);
            final ImmutableSet<MethodWellDefinedness> mwds =
                getWdMethodChecks(targetKJT, targetMethod);
            if (!mwds.isEmpty()) {
                assert mwds.size() == 1;
                final MethodWellDefinedness oldMwd = mwds.iterator().next();
                unregisterContract(oldMwd);
                mwd = mwd.combine(oldMwd, services);
            }
            registerContract(mwd);
        } else if (contract instanceof WellDefinednessCheck) {
            registerWdCheck((WellDefinednessCheck) contract);
        }
        contractsByName.put(contract.getName(), contract);
        final ImmutableSet<IObserverFunction> oldTargets = getContractTargets(targetKJT);
        final ImmutableSet<IObserverFunction> newTargets = oldTargets.add(targetMethod);
        contractTargets.put(targetKJT, newTargets);
    }

    /**
     * Removes the contract from the repository, but keeps its target.
     */
    private void unregisterContract(Contract contract) {
        final KeYJavaType kjt = contract.getKJT();
        final Pair<KeYJavaType, IObserverFunction> tp = new Pair<>(kjt, contract.getTarget());
        contracts.put(tp, contracts.get(tp).remove(contract));
        if (contract instanceof FunctionalOperationContract) {
            final Pair<KeYJavaType, IProgramMethod> tp2 =
                new Pair<>(tp.first, (IProgramMethod) tp.second);
            operationContracts.put(tp2,
                operationContracts.get(tp2).remove((FunctionalOperationContract) contract));
            if (!getWdChecks(contract.getKJT(), contract.getTarget()).isEmpty()) {
                ImmutableSet<WellDefinednessCheck> wdcs =
                    getWdChecks(contract.getKJT(), contract.getTarget());
                for (WellDefinednessCheck wdc : wdcs) {
                    if (wdc instanceof MethodWellDefinedness
                            && ((MethodWellDefinedness) wdc).getMethodContract().equals(contract)) {
                        unregisterWdCheck(wdc);
                    }
                }
            }
        }
        if (contract instanceof WellDefinednessCheck) {
            unregisterWdCheck((WellDefinednessCheck) contract);
        }
        contractsByName.remove(contract.getName());
    }

    /**
     * Adds initially clause as post-condition to contracts of constructors. Creates a new contract
     * if there is none yet.
     *
     * @param inv initially clause
     * @param kjt constructors of this type are added a post-condition
     * @throws SLTranslationException during contract construction from history constraint
     */
    private void createContractsFromInitiallyClause(InitiallyClause inv, KeYJavaType kjt)
            throws SLTranslationException {
        if (!kjt.equals(inv.getKJT())) {
            inv = inv.setKJT(kjt);
        }
        for (IProgramMethod pm : services.getJavaInfo().getConstructors(kjt)) {
            if (!JMLInfoExtractor.isHelper(pm)) {
                final ImmutableSet<Contract> oldContracts = getContracts(kjt, pm);
                ImmutableSet<FunctionalOperationContract> oldFuncContracts =
                    DefaultImmutableSet.nil();
                for (Contract old : oldContracts) {
                    if (old instanceof FunctionalOperationContract) {
                        oldFuncContracts = oldFuncContracts.add((FunctionalOperationContract) old);
                    }
                }
                if (oldFuncContracts.isEmpty()) {
                    final FunctionalOperationContract iniContr = cf.func(pm, inv);
                    addContractNoInheritance(iniContr);
                    assert getContracts(kjt, pm).size() == (WellDefinednessCheck.isOn() ? 2 : 1)
                            + oldContracts.size();
                } else {
                    for (FunctionalOperationContract c : oldFuncContracts) {
                        unregisterContract(c);
                        addContractNoInheritance(cf.addPost(c, inv));
                        assert contractTargets.get(kjt).contains(c.getTarget());
                    }
                    assert getContracts(kjt, pm).size() == oldContracts.size();
                }
            }
        }
    }

    // Internal interface for well-definedness checks

    /**
     * Remove well-definedness checks from a given set of contracts
     *
     * @param contracts A set of contracts
     * @return contracts without well-definedness checks
     */
    private static ImmutableSet<Contract> removeWdChecks(ImmutableSet<Contract> contracts) {
        ImmutableList<Contract> result = ImmutableSLList.nil();
        if (contracts == null) {
            return contracts;
        }
        for (Contract c : contracts) {
            if (!(c instanceof WellDefinednessCheck)) {
                result = result.prepend(c);
            }
        }
        return DefaultImmutableSet.fromImmutableList(result);
    }

    /**
     * Registers a well-definedness check. It does not take care of its visibility in the proof
     * management dialog (this is done in {@link #registerContract(Contract, Pair)}).
     *
     * @param check The well-definedness check to be registered
     */
    private void registerWdCheck(WellDefinednessCheck check) {
        ImmutableSet<WellDefinednessCheck> checks =
            getWdChecks(check.getKJT(), check.getTarget()).add(check);
        wdChecks.put(new Pair<>(check.getKJT(), check.getTarget()), checks);
    }

    /**
     * Unregisters a well-definedness check. It does not take care of its visibility in the proof
     * management dialog.
     *
     * @param check The well-definedness check to be unregistered
     */
    private void unregisterWdCheck(WellDefinednessCheck check) {
        wdChecks.put(new Pair<>(check.getKJT(), check.getTarget()),
            getWdChecks(check.getKJT(), check.getTarget()).remove(check));
    }

    /**
     * Returns all registered (atomic) well-definedness checks for the passed kjt.
     */
    private ImmutableSet<WellDefinednessCheck> getWdChecks(KeYJavaType kjt) {
        assert kjt != null;
        ImmutableSet<WellDefinednessCheck> result = DefaultImmutableSet.nil();
        for (WellDefinednessCheck ch : getAllWdChecks()) {
            if (ch.getKJT().equals(kjt)) {
                result = result.add(ch);
            }
        }
        return result;
    }

    /**
     * Returns all registered (atomic) well-definedness checks for the passed target and kjt.
     */
    private ImmutableSet<WellDefinednessCheck> getWdChecks(KeYJavaType kjt,
            IObserverFunction target) {
        assert kjt != null;
        assert target != null;
        target = getCanonicalFormForKJT(target, kjt);
        final Pair<KeYJavaType, IObserverFunction> pair = new Pair<>(kjt, target);
        final ImmutableSet<WellDefinednessCheck> result = wdChecks.get(pair);
        return result == null ? DefaultImmutableSet.nil() : result;
    }

    /**
     * Returns all registered well-definedness checks for method contracts.
     */
    private ImmutableSet<MethodWellDefinedness> getAllWdMethodChecks() {
        ImmutableSet<MethodWellDefinedness> result = DefaultImmutableSet.nil();
        for (var s : getAllWdChecks()) {
            if (s instanceof MethodWellDefinedness) {
                result = result.add((MethodWellDefinedness) s);
            }
        }
        return result;
    }

    /**
     * Returns all registered (atomic) well-definedness method checks for the passed kjt.
     */
    private ImmutableSet<MethodWellDefinedness> getWdMethodChecks(KeYJavaType kjt) {
        assert kjt != null;
        ImmutableSet<MethodWellDefinedness> result = DefaultImmutableSet.nil();
        for (MethodWellDefinedness ch : getAllWdMethodChecks()) {
            if (ch.getKJT().equals(kjt)) {
                result = result.add(ch);
            }
        }
        return result;
    }

    /**
     * Returns all registered (atomic) well-definedness method checks for the passed target and kjt.
     */
    private ImmutableSet<MethodWellDefinedness> getWdMethodChecks(KeYJavaType kjt,
            IObserverFunction target) {
        assert kjt != null;
        assert target != null;
        ImmutableSet<MethodWellDefinedness> result = DefaultImmutableSet.nil();
        for (MethodWellDefinedness ch : getAllWdMethodChecks()) {
            if (ch.getKJT().equals(kjt) && ch.getTarget().equals(target)) {
                result = result.add(ch);
            }
        }
        return result;
    }

    /**
     * Returns all registered (atomic) well-definedness class checks for the passed kjt.
     */
    private ImmutableSet<ClassWellDefinedness> getWdClassChecks(KeYJavaType kjt) {
        ImmutableSet<WellDefinednessCheck> checks = getWdChecks(kjt);
        ImmutableSet<ClassWellDefinedness> invs = DefaultImmutableSet.nil();
        for (WellDefinednessCheck check : checks) {
            if (check instanceof ClassWellDefinedness) {
                invs = invs.add((ClassWellDefinedness) check);
            }
        }
        return invs;
    }

    /**
     * Helper for {@link #map(UnaryOperator, Services)}.
     *
     * @param map a map.
     * @param op an operator.
     * @param services services.
     */
    @SuppressWarnings("unchecked")
    private <K, V extends SpecificationElement> void mapValueSets(Map<K, ImmutableSet<V>> map,
            UnaryOperator<Term> op, Services services) {
        for (Entry<K, ImmutableSet<V>> entry : map.entrySet()) {
            final K key = entry.getKey();
            final ImmutableSet<V> oldSet = entry.getValue();
            ImmutableSet<V> newSet = DefaultImmutableSet.nil();

            for (V oldContract : oldSet) {
                V newContract = (V) oldContract.map(op, services);
                newSet = newSet.add(newContract);

                assert oldContract.getName().equals(newContract.getName());
                if (oldContract instanceof Contract
                        && contractsByName.containsKey(oldContract.getName())) {
                    contractsByName.put(oldContract.getName(), (Contract) newContract);
                }
            }

            map.put(key, (ImmutableSet<V>) oldSet.stream()
                    .map(contract -> contract.map(op, services)).collect(ImmutableSet.collector()));
        }
    }

    /**
     * Helper for {@link #map(UnaryOperator, Services)}.
     *
     * @param map a map.
     * @param op an operator.
     * @param services services.
     */
    @SuppressWarnings("unchecked")
    private <K, V extends SpecificationElement> void mapValues(Map<K, V> map,
            UnaryOperator<Term> op, Services services) {
        for (Entry<K, V> entry : map.entrySet()) {
            final K key = entry.getKey();
            final V oldContract = entry.getValue();
            final V newContract = (V) oldContract.map(op, services);
            map.put(key, newContract);

            assert oldContract.getName().equals(newContract.getName());
            if (oldContract instanceof Contract
                    && contractsByName.containsKey(oldContract.getName())) {
                contractsByName.put(oldContract.getName(), (Contract) newContract);
            }
        }
    }

    // -------------------------------------------------------------------------
    // public interface
    // -------------------------------------------------------------------------

    /**
     * Applies the specified operator to every contract in this repository.
     *
     * @param op an operator.
     * @param services services.
     * @see SpecificationElement#map(java.util.function.UnaryOperator, Services)
     */
    public void map(UnaryOperator<Term> op, Services services) {
        mapValueSets(contracts, op, services);
        mapValueSets(operationContracts, op, services);
        mapValueSets(wdChecks, op, services);
        mapValueSets(invs, op, services);
        mapValueSets(axioms, op, services);
        mapValueSets(initiallyClauses, op, services);
        mapValues(loopInvs, op, services);
        mapValueSets(blockContracts, op, services);
        mapValueSets(loopContracts, op, services);
        mapValueSets(mergeContracts, op, services);
        mapValueSets(allClassAxiomsCache, op, services);
    }

    /**
     * Returns all registered contracts.
     */
    public ImmutableSet<Contract> getAllContracts() {
        ImmutableSet<Contract> result = DefaultImmutableSet.nil();
        for (ImmutableSet<Contract> s : contracts.values()) {
            result = result.union(s);
        }
        return WellDefinednessCheck.isOn() ? result : removeWdChecks(result);
    }

    /**
     * Returns all registered (atomic) contracts for the passed target.
     */
    public ImmutableSet<Contract> getContracts(KeYJavaType kjt, IObserverFunction target) {
        target =
            getCanonicalFormForKJT(Objects.requireNonNull(target), Objects.requireNonNull(kjt));
        final Pair<KeYJavaType, IObserverFunction> pair = new Pair<>(kjt, target);
        final ImmutableSet<Contract> result =
            WellDefinednessCheck.isOn() ? contracts.get(pair) : removeWdChecks(contracts.get(pair));
        return result == null ? DefaultImmutableSet.nil() : result;
    }

    /**
     * Returns all registered (atomic) operation contracts for the passed operation.
     */
    public ImmutableSet<FunctionalOperationContract> getOperationContracts(KeYJavaType kjt,
            IProgramMethod pm) {
        pm = (IProgramMethod) getCanonicalFormForKJT(pm, kjt);
        final Pair<KeYJavaType, IProgramMethod> pair = new Pair<>(kjt, pm);
        final ImmutableSet<FunctionalOperationContract> result = operationContracts.get(pair);
        return result == null ? DefaultImmutableSet.nil() : result;
    }

    /**
     * Returns all registered (atomic) operation contracts for the passed operation which refer to
     * the passed modality.
     */
    public ImmutableSet<FunctionalOperationContract> getOperationContracts(KeYJavaType kjt,
            IProgramMethod pm, Modality.JavaModalityKind modalityKind) {
        ImmutableSet<FunctionalOperationContract> result = getOperationContracts(kjt, pm);
        final boolean transactionModality =
            modalityKind.transaction();
        final Modality.JavaModalityKind matchModality = transactionModality
                ? ((modalityKind == Modality.JavaModalityKind.DIA_TRANSACTION)
                        ? Modality.JavaModalityKind.DIA
                        : Modality.JavaModalityKind.BOX)
                : modalityKind;
        for (FunctionalOperationContract contract : result) {
            if (!contract.getModalityKind().equals(matchModality)
                    || (transactionModality && !contract.transactionApplicableContract())) {
                result = result.remove(contract);
            }
        }
        return result;
    }

    /**
     * Returns the registered (atomic or combined) contract corresponding to the passed name, or
     * null.
     */
    public Contract getContractByName(String name) {
        if (name == null || name.isEmpty()) {
            return null;
        }
        String[] baseNames = name.split(CONTRACT_COMBINATION_MARKER);
        if (baseNames.length == 1) {
            return contractsByName.get(baseNames[0]);
        }

        ImmutableSet<FunctionalOperationContract> baseContracts = DefaultImmutableSet.nil();
        for (String baseName : baseNames) {
            FunctionalOperationContract baseContract =
                (FunctionalOperationContract) contractsByName.get(baseName);
            if (baseContract == null) {
                return null;
            }
            baseContracts = baseContracts.add(baseContract);
        }

        return combineOperationContracts(baseContracts);
    }

    /**
     * Returns a set encompassing the passed contract and all its versions inherited to overriding
     * methods.
     */
    public ImmutableSet<Contract> getInheritedContracts(Contract contract) {
        ImmutableSet<Contract> result = DefaultImmutableSet.<Contract>nil().add(contract);
        final ImmutableSet<Pair<KeYJavaType, IObserverFunction>> subs =
            getOverridingTargets(contract.getKJT(), contract.getTarget());
        for (Pair<KeYJavaType, IObserverFunction> sub : subs) {
            for (Contract subContract : getContracts(sub.first, sub.second)) {
                if (subContract.id() == contract.id()) {
                    result = result.add(subContract);
                    break;
                }
            }
        }
        return result;
    }

    /**
     * Returns a set encompassing the passed contracts and all its versions inherited to overriding
     * methods.
     */
    public ImmutableSet<Contract> getInheritedContracts(ImmutableSet<Contract> contractSet) {
        ImmutableSet<Contract> result = DefaultImmutableSet.nil();
        for (Contract c : contractSet) {
            result = result.union(getInheritedContracts(c));
        }
        return result;
    }

    /**
     * Returns all functions for which contracts are registered in the passed type.
     */
    public ImmutableSet<IObserverFunction> getContractTargets(KeYJavaType kjt) {
        final ImmutableSet<IObserverFunction> result = contractTargets.get(kjt);
        return result == null ? DefaultImmutableSet.nil() : result;
    }

    /**
     * Registers the passed (atomic) contract, and inherits it to all overriding methods.
     */
    public void addContract(Contract contract) {
        contract = prepareContract(contract);

        // register and inherit
        final ImmutableSet<Pair<KeYJavaType, IObserverFunction>> impls =
            getOverridingTargets(contract.getKJT(), contract.getTarget())
                    .add(new Pair<>(contract.getKJT(), contract.getTarget()));

        registerContract(contract, impls);
        if (!contractTargets.get(contract.getKJT()).contains(contract.getTarget())) {
            throw new IllegalStateException(
                "target " + contract.getTarget() + " missing for contract " + contract);
        }
    }

    /**
     * Registers the passed (atomic) contract without inheriting it.
     */
    public void addContractNoInheritance(Contract contract) {
        registerContract(prepareContract(contract));
    }

    /**
     * Registers the passed contracts.
     */
    public void addContracts(ImmutableSet<Contract> toAdd) {
        for (Contract contract : toAdd) {
            addContract(contract);
        }
    }

    /**
     * Creates a combined contract out of the passed atomic contracts.
     */
    public FunctionalOperationContract combineOperationContracts(
            ImmutableSet<FunctionalOperationContract> toCombine) {
        assert toCombine != null && !toCombine.isEmpty();
        for (Contract contract : toCombine) {
            assert !contract.getName().contains(CONTRACT_COMBINATION_MARKER)
                    : "Please combine only atomic contracts!";
        }

        // sort contracts alphabetically (for determinism)
        FunctionalOperationContract[] contractsArray =
            toCombine.toArray(new FunctionalOperationContract[toCombine.size()]);
        Arrays.sort(contractsArray, Comparator.comparing(SpecificationElement::getName));

        return cf.union(contractsArray);
    }

    /**
     * Splits the passed contract into its atomic components.
     */
    public ImmutableSet<Contract> splitContract(Contract contract) {
        ImmutableSet<Contract> result = DefaultImmutableSet.nil();
        String[] atomicNames = contract.getName().split(CONTRACT_COMBINATION_MARKER);
        for (String atomicName : atomicNames) {
            Contract atomicContract = contractsByName.get(atomicName);
            if (atomicContract == null) {
                // This case happens in the symbolic execution debugger when
                // a temporary contract is used which is not part of the
                // SpecificationRepository
                return DefaultImmutableSet.nil(); // Null can not
                // returned,
                // because it
                // causes many
                // NullPointerExceptions
            }
            assert atomicContract.getTarget().equals(contract.getTarget());
            result = result.add(atomicContract);
        }
        return result;
    }

    /**
     * Registers the passed class invariant, and inherits it to all subclasses if it is public or
     * protected.
     */
    public void addClassInvariant(ClassInvariant inv) {
        final KeYJavaType kjt = inv.getKJT();
        final IObserverFunction target = inv.isStatic() ? services.getJavaInfo().getStaticInv(kjt)
                : services.getJavaInfo().getInv();
        invs.put(kjt, getClassInvariants(kjt).add(inv));
        final ImmutableSet<ClassWellDefinedness> cwds = getWdClassChecks(kjt);
        if (cwds.isEmpty()) {
            registerContract(new ClassWellDefinedness(inv, target, null, null, services));
        } else {
            assert cwds.size() == 1;
            ClassWellDefinedness cwd = cwds.iterator().next();
            unregisterContract(cwd);
            cwd = cwd.combine(new ClassWellDefinedness(inv, cwd.getTarget(), null, null, services),
                services);
            registerContract(cwd);
        }

        // in any case, create axiom with non-static target
        addClassAxiom(new PartialInvAxiom(inv, false, services));
        // for a static invariant, create also an axiom with a static target
        if (inv.isStatic()) {
            addClassAxiom(new PartialInvAxiom(inv, true, services));
        }
        // inherit non-private, non-static invariants
        if (!inv.isStatic() && VisibilityModifier.allowsInheritance(inv.getVisibility())) {
            final ImmutableList<KeYJavaType> subs = services.getJavaInfo().getAllSubtypes(kjt);
            for (KeYJavaType sub : subs) {
                ClassInvariant subInv = inv.setKJT(sub);
                final IObserverFunction subTarget =
                    subInv.isStatic() ? services.getJavaInfo().getStaticInv(sub)
                            : services.getJavaInfo().getInv();
                invs.put(sub, getClassInvariants(sub).add(subInv));
                final ImmutableSet<ClassWellDefinedness> subCwds = getWdClassChecks(sub);
                if (subCwds.isEmpty()) {
                    registerContract(
                        new ClassWellDefinedness(subInv, subTarget, null, null, services));
                } else {
                    for (ClassWellDefinedness cwd : subCwds) {
                        unregisterContract(cwd);
                        cwd.addInv(subInv.getInv(cwd.getOrigVars().self, services));
                        registerContract(cwd);
                    }
                }
            }
        }
    }

    /**
     * Registers the passed class invariants.
     */
    public void addClassInvariants(ImmutableSet<ClassInvariant> toAdd) {
        for (ClassInvariant inv : toAdd) {
            addClassInvariant(inv);
        }
    }

    /**
     * Adds postconditions raising from initially clauses to all constructors. <b>Warning</b>: To be
     * called after all contracts have been registered.
     *
     * @throws SLTranslationException may be thrown during contract extraction
     */
    public void createContractsFromInitiallyClauses() throws SLTranslationException {
        for (KeYJavaType kjt : initiallyClauses.keySet()) {
            for (InitiallyClause inv : initiallyClauses.get(kjt)) {
                createContractsFromInitiallyClause(inv, kjt);
                if (VisibilityModifier.allowsInheritance(inv.getVisibility())) {
                    final ImmutableList<KeYJavaType> subs =
                        services.getJavaInfo().getAllSubtypes(kjt);
                    for (KeYJavaType sub : subs) {
                        createContractsFromInitiallyClause(inv, sub);
                    }
                }
            }
        }
    }

    /**
     * Registers the passed initially clause. Initially clauses in JML specify the post-state of any
     * constructor of subtypes; they may particularly be used in interface types. To create proof
     * obligations from initially clauses, the method
     * <code>createContractsFromInitiallyClauses</code> adds them to the contracts of respective
     * constructors (or adds a contract if there is none yet).
     *
     * @param ini initially clause
     */
    public void addInitiallyClause(InitiallyClause ini) {
        ImmutableSet<InitiallyClause> oldClauses = initiallyClauses.get(ini.getKJT());
        if (oldClauses == null) {
            oldClauses = DefaultImmutableSet.nil();
        }
        initiallyClauses.put(ini.getKJT(), oldClauses.add(ini));
    }

    /**
     * Registers the passed initially clauses.
     */
    public void addInitiallyClauses(ImmutableSet<InitiallyClause> toAdd) {
        for (InitiallyClause inv : toAdd) {
            addInitiallyClause(inv);
        }
    }

    /**
     * Returns all class axioms visible in the passed class, including the axioms induced by
     * invariant declarations.
     */
    public ImmutableSet<ClassAxiom> getClassAxioms(KeYJavaType selfKjt) {
        ImmutableSet<ClassAxiom> result = allClassAxiomsCache.get(selfKjt);
        if (result == null) {
            // get visible registered axioms of other classes
            result = getVisibleAxiomsOfOtherClasses(selfKjt);
            // add registered axioms of own class
            ImmutableSet<ClassAxiom> ownAxioms = axioms.get(selfKjt);
            if (ownAxioms != null) {
                for (ClassAxiom ax : ownAxioms) {
                    result = result.add(ax);
                }
            }

            final JavaInfo ji = services.getJavaInfo();

            // add invariant axiom for own class and other final classes
            for (KeYJavaType kjt : services.getJavaInfo().getAllKeYJavaTypes()) {
                if (kjt != selfKjt && !ji.isFinal(kjt)) {
                    continue; // only final classes
                }
                if (kjt != selfKjt && JavaInfo.isPrivate(kjt)) {
                    continue; // only non-private classes
                }
                final ImmutableSet<ClassInvariant> myInvs = getClassInvariants(kjt);
                final ProgramVariable selfVar = tb.selfVar(kjt, false);

                Term invDef = tb.tt();
                Term staticInvDef = tb.tt();
                Term freeInvDef = tb.tt();
                Term freeStaticInvDef = tb.tt();

                for (ClassInvariant inv : myInvs) {
                    if (!inv.isFree()) {
                        invDef = tb.and(invDef, inv.getInv(selfVar, services));
                    } else {
                        freeInvDef = tb.and(freeInvDef, inv.getInv(selfVar, services));
                    }

                    if (inv.isStatic()) {
                        if (!inv.isFree()) {
                            staticInvDef = tb.and(staticInvDef, inv.getInv(null, services));
                        } else {
                            freeStaticInvDef =
                                tb.and(freeStaticInvDef, inv.getInv(selfVar, services));
                        }
                    }
                }

                invDef = tb.tf().createTerm(Equality.EQV, tb.inv(tb.var(selfVar)), invDef);
                staticInvDef = tb.tf().createTerm(Equality.EQV, tb.staticInv(kjt), staticInvDef);
                freeInvDef = tb.tf().createTerm(Equality.EQV,
                    tb.invFree(tb.var(selfVar)), freeInvDef);
                freeStaticInvDef = tb.tf().createTerm(Equality.EQV,
                    tb.staticInvFree(kjt), freeStaticInvDef);

                final IObserverFunction invSymbol = services.getJavaInfo().getInv();
                final IObserverFunction staticInvSymbol = services.getJavaInfo().getStaticInv(kjt);
                final IObserverFunction freeInvSymbol = services.getJavaInfo().getInvFree();
                final IObserverFunction freeStaticInvSymbol = services.getJavaInfo()
                        .getStaticInvFree(kjt);

                final ClassAxiom invRepresentsAxiom =
                    new RepresentsAxiom("Class invariant axiom for " + kjt.getFullName(), invSymbol,
                        kjt, new Private(), null, invDef, selfVar, ImmutableSLList.nil(), null);
                result = result.add(invRepresentsAxiom);

                final ClassAxiom staticInvRepresentsAxiom = new RepresentsAxiom(
                    "Static class invariant axiom for " + kjt.getFullName(), staticInvSymbol, kjt,
                    new Private(), null, staticInvDef, null, ImmutableSLList.nil(), null);
                result = result.add(staticInvRepresentsAxiom);

                final ClassAxiom invFreeRepresentsAxiom = new RepresentsAxiom(
                    "Free class invariant axiom for " + kjt.getFullName(), freeInvSymbol, kjt,
                    new Private(), null, freeInvDef, selfVar, ImmutableSLList.nil(), null);
                result = result.add(invFreeRepresentsAxiom);

                final ClassAxiom staticFreeInvRepresentsAxiom = new RepresentsAxiom(
                    "Free static class invariant axiom for " + kjt.getFullName(),
                    freeStaticInvSymbol, kjt, new Private(), null, freeStaticInvDef, null,
                    ImmutableSLList.nil(), null);
                result = result.add(staticFreeInvRepresentsAxiom);

            }
            // add query axioms for own class
            for (IProgramMethod pm : services.getJavaInfo().getAllProgramMethods(selfKjt)) {
                if (!pm.isVoid() && !pm.isConstructor() && !pm.isImplicit() && !pm.isModel()) {
                    pm = services.getJavaInfo().getToplevelPM(selfKjt, pm);

                    var sb = new StringBuilder();
                    for (KeYJavaType pd : pm.getParamTypes()) {
                        sb.append(pd.getJavaType().getFullName());
                        sb.append("_");
                    }

                    final ClassAxiom queryAxiom = new QueryAxiom("Query axiom for " + pm.getName()
                        + "_" + sb + " in " + selfKjt.getFullName(), pm, selfKjt);
                    result = result.add(queryAxiom);
                }
            }

            // add model method axioms of all kinds
            result = result.union(getModelMethodAxioms());
            // add axioms for enclosing class, if applicable
            final KeYJavaType enclosingKJT = getEnclosingKJT(selfKjt);
            if (enclosingKJT != null) {
                result = result.union(getClassAxioms(enclosingKJT));
            }
            allClassAxiomsCache.put(selfKjt, result);
        }
        return result;
    }

    private ImmutableSet<ClassAxiom> getModelMethodAxioms() {
        ImmutableSet<ClassAxiom> result = DefaultImmutableSet.nil();
        for (KeYJavaType kjt : services.getJavaInfo().getAllKeYJavaTypes()) {
            for (IProgramMethod pm : services.getJavaInfo().getAllProgramMethods(kjt)) {
                final ProgramVariable selfVar = pm.isStatic() ? null : tb.selfVar(kjt, false);
                if (!pm.isVoid() && pm.isModel()) {
                    pm = services.getJavaInfo().getToplevelPM(kjt, pm);
                    ImmutableList<ProgramVariable> paramVars = tb.paramVars(pm, false);
                    Map<LocationVariable, ProgramVariable> atPreVars = new LinkedHashMap<>();
                    List<LocationVariable> heaps = HeapContext.getModHeaps(services, false);
                    for (LocationVariable heap : heaps) {
                        atPreVars.put(heap,
                            tb.atPreVar(heap.name().toString(), heap.sort(), false));
                    }
                    ProgramVariable resultVar = tb.resultVar(pm, false);

                    // This assumes there is one operation contract for each
                    // model pm per class
                    // We need to construct an inheritance chain of contracts
                    // starting at the bottom
                    ImmutableList<FunctionalOperationContract> lookupContracts =
                        ImmutableSLList.nil();
                    ImmutableSet<FunctionalOperationContract> cs = getOperationContracts(kjt, pm);
                    ImmutableList<KeYJavaType> superTypes =
                        services.getJavaInfo().getAllSupertypes(kjt);
                    for (KeYJavaType superType : superTypes) {
                        for (FunctionalOperationContract fop : cs) {
                            if (fop.getSpecifiedIn().equals(superType)) {
                                lookupContracts = lookupContracts.append(fop);
                            }
                        }
                    }
                    for (FunctionalOperationContract fop : lookupContracts) {
                        Term representsFromContract = fop.getRepresentsAxiom(heaps.get(0), selfVar,
                            paramVars, tb.resultVar(pm, false), atPreVars, services);
                        Term preContract =
                            fop.getPre(heaps, selfVar, paramVars, atPreVars, services);
                        if (preContract == null) {
                            preContract = tb.tt();
                        }
                        if (representsFromContract != null) {
                            // TODO Wojtek: I do not understand the visibility
                            // issues of model fields/methods.
                            // VisibilityModifier visibility = pm.isPrivate() ?
                            // new Private() :
                            // (pm.isProtected() ? new Protected() :
                            // (pm.isPublic() ? new Public() : null));
                            final ClassAxiom modelMethodRepresentsAxiom =
                                new RepresentsAxiom(
                                    "Definition axiom for " + pm.getName() + " in "
                                        + kjt.getFullName(),
                                    pm, kjt, new Private(), preContract, representsFromContract,
                                    selfVar, paramVars, atPreVars);
                            result = result.add(modelMethodRepresentsAxiom);
                            break;
                        }
                    }
                    for (FunctionalOperationContract fop : getOperationContracts(kjt, pm)) {
                        if (!fop.getSpecifiedIn().equals(kjt)) {
                            continue;
                        }
                        Term preFromContract =
                            fop.getPre(heaps, selfVar, paramVars, atPreVars, services);
                        Term freePreFromContract =
                            fop.getFreePre(heaps, selfVar, paramVars, atPreVars, services);
                        Term postFromContract = fop.getPost(heaps, selfVar, paramVars, resultVar,
                            null, atPreVars, services);
                        Term freePostFromContract = fop.getFreePost(heaps, selfVar, paramVars,
                            resultVar, null, atPreVars, services);
                        if (preFromContract != null
                                && ((postFromContract != null && postFromContract != tb.tt())
                                        || (freePostFromContract != null
                                                && freePostFromContract != tb.tt()))) {
                            Term mbyFromContract =
                                fop.hasMby() ? fop.getMby(selfVar, paramVars, services) : null;
                            final ClassAxiom modelMethodContractAxiom = new ContractAxiom(
                                "Contract axiom for " + pm.getName() + " in " + kjt.getName(), pm,
                                kjt, new Private(), preFromContract, freePreFromContract,
                                postFromContract, freePostFromContract, mbyFromContract, atPreVars,
                                selfVar, resultVar, paramVars);
                            result = result.add(modelMethodContractAxiom);
                        }
                    }
                }
            }
        }
        return result;
    }

    /**
     * Registers the passed class axiom.
     */
    public void addClassAxiom(ClassAxiom ax) {
        KeYJavaType kjt = ax.getKJT();
        ImmutableSet<ClassAxiom> currentAxioms = axioms.get(kjt);
        if (currentAxioms == null) {
            currentAxioms = DefaultImmutableSet.nil();
        }
        if (ax instanceof RepresentsAxiom) {
            // there may only be one conjoined represents axiom per model field
            RepresentsAxiom oldRep = getRepresentsAxiom(kjt, ax);
            if (oldRep != null) {
                final RepresentsAxiom newRep = oldRep.conjoin((RepresentsAxiom) ax, tb);
                axioms.put(kjt, currentAxioms.remove(oldRep).add(newRep));
            } else {
                axioms.put(kjt, currentAxioms.add(ax));
            }
            // inherit represents clauses to subclasses and conjoin together
            if (VisibilityModifier.allowsInheritance(ax.getVisibility())) {
                final ImmutableList<KeYJavaType> subs = services.getJavaInfo().getAllSubtypes(kjt);
                for (KeYJavaType sub : subs) {
                    RepresentsAxiom subAx = ((RepresentsAxiom) ax).setKJT(sub);
                    currentAxioms = axioms.get(sub);
                    if (currentAxioms == null) {
                        currentAxioms = DefaultImmutableSet.nil();
                    }
                    oldRep = getRepresentsAxiom(sub, subAx);
                    if (oldRep == null) {
                        axioms.put(sub, currentAxioms.add(subAx));
                    } else {
                        final RepresentsAxiom newSubRep = oldRep.conjoin(subAx, tb);
                        axioms.put(sub, currentAxioms.remove(oldRep).add(newSubRep));
                    }
                }
            }
        } else {
            axioms.put(kjt, currentAxioms.add(ax));
        }
    }

    /**
     * Registers the passed class axioms.
     */
    public void addClassAxioms(ImmutableSet<ClassAxiom> toAdd) {
        for (ClassAxiom ax : toAdd) {
            addClassAxiom(ax);
        }
    }

    /**
     * Returns all proofs registered for the passed PO (or stronger POs).
     */
    public ImmutableSet<Proof> getProofs(ProofOblInput po) {
        ImmutableSet<Proof> result = DefaultImmutableSet.nil();
        for (Map.Entry<ProofOblInput, ImmutableSet<Proof>> entry : proofs.entrySet()) {
            ProofOblInput mapPO = entry.getKey();
            ImmutableSet<Proof> sop = entry.getValue();
            if (mapPO.implies(po)) {
                result = result.union(sop);
            }
        }
        return result;
    }

    /**
     * Returns all proofs registered for the passed atomic contract, or for combined contracts
     * including the passed atomic contract
     */
    public ImmutableSet<Proof> getProofs(Contract atomicContract) {
        assert !atomicContract.getName().contains(CONTRACT_COMBINATION_MARKER)
                : "Contract must be atomic";

        ImmutableSet<Proof> result = DefaultImmutableSet.nil();
        for (Map.Entry<ProofOblInput, ImmutableSet<Proof>> entry : proofs.entrySet()) {
            final ProofOblInput po = entry.getKey();
            if (po instanceof ContractPO) {
                final Contract poContract = ((ContractPO) po).getContract();
                if (splitContract(poContract).contains(atomicContract)) {
                    result = result.union(entry.getValue());
                }
            }
        }
        return result;
    }

    /**
     * Returns all proofs registered for the passed target and its overriding targets.
     */
    public ImmutableSet<Proof> getProofs(KeYJavaType kjt, IObserverFunction target) {
        final ImmutableSet<Pair<KeYJavaType, IObserverFunction>> targets =
            getOverridingTargets(kjt, target).add(new Pair<>(kjt, target));
        ImmutableSet<Proof> result = DefaultImmutableSet.nil();
        for (Map.Entry<ProofOblInput, ImmutableSet<Proof>> entry : proofs.entrySet()) {
            final ProofOblInput po = entry.getKey();
            final ImmutableSet<Proof> sop = entry.getValue();
            if (po instanceof ContractPO) {
                final Contract contract = ((ContractPO) po).getContract();
                final Pair<KeYJavaType, IObserverFunction> pair =
                    new Pair<>(contract.getKJT(), contract.getTarget());
                if (targets.contains(pair)) {
                    result = result.union(sop);
                }
            }
        }
        return result;
    }

    /**
     * Returns all proofs registered with this specification repository.
     */
    public ImmutableSet<Proof> getAllProofs() {
        ImmutableSet<Proof> result = DefaultImmutableSet.nil();
        Collection<ImmutableSet<Proof>> proofSets = proofs.values();
        for (ImmutableSet<Proof> proofSet : proofSets) {
            result = result.union(proofSet);
        }
        return result;
    }

    /**
     * Returns the PO that the passed proof is about, or null.
     */
    public ContractPO getContractPOForProof(Proof proof) {
        ProofOblInput po = getProofOblInput(proof);
        if (po instanceof ContractPO) {
            return (ContractPO) po;
        } else {
            return null;
        }
    }

    /**
     * Returns the PO that the passed contract is about, or null.
     */
    public ContractPO getPO(Contract c) {
        for (ProofOblInput po : proofs.keySet()) {
            if (po instanceof ContractPO && ((ContractPO) po).getContract().equals(c)) {
                return (ContractPO) po;
            }
        }
        return null;
    }

    public ContractPO getPOForProof(Proof proof) {
        for (Map.Entry<ProofOblInput, ImmutableSet<Proof>> entry : proofs.entrySet()) {
            ProofOblInput po = entry.getKey();
            ImmutableSet<Proof> sop = entry.getValue();
            if (sop.contains(proof) && po instanceof ContractPO) {
                return (ContractPO) po;
            }
        }
        return null;
    }

    /**
     * Returns the {@link ProofOblInput} from which the given {@link Proof} was created.
     *
     * @param proof The {@link Proof}.
     * @return The {@link ProofOblInput} of the given {@link Proof} or {@code null} if not
     *         available.
     */
    public ProofOblInput getProofOblInput(Proof proof) {
        for (Map.Entry<ProofOblInput, ImmutableSet<Proof>> entry : proofs.entrySet()) {
            ProofOblInput po = entry.getKey();
            ImmutableSet<Proof> sop = entry.getValue();
            if (sop.contains(proof)) {
                return po;
            }
        }
        return null;
    }

    /**
     * Returns the target that the passed proof is about, or null.
     */
    public IObserverFunction getTargetOfProof(Proof proof) {
        final ContractPO po = getPOForProof(proof);
        return po == null ? null : po.getContract().getTarget();
    }

    /**
     * Registers the passed proof.
     */
    public void registerProof(ProofOblInput po, Proof proof) {
        proofs.put(po, getProofs(po).add(proof));
    }

    /**
     * Unregisters the passed proof.
     */
    public void removeProof(Proof proof) {
        for (Map.Entry<ProofOblInput, ImmutableSet<Proof>> entry : proofs.entrySet()) {
            ImmutableSet<Proof> sop = entry.getValue();
            if (sop.contains(proof)) {
                sop = sop.remove(proof);
                if (sop.isEmpty()) {
                    proofs.remove(entry.getKey());
                } else {
                    proofs.put(entry.getKey(), sop);
                }
                return;
            }
        }
    }

    /**
     * Returns the registered loop invariant for the passed loop, or null.
     */
    public LoopSpecification getLoopSpec(LoopStatement loop) {
        final int line = loop.getStartPosition().line();
        Pair<LoopStatement, Integer> l = new Pair<>(loop, line);
        LoopSpecification inv = loopInvs.get(l);
        if (inv == null && line != -1) {
            l = new Pair<>(loop, -1);
            inv = loopInvs.get(l);
        }
        return inv;
    }

    /**
     * Copies a loop invariant from a loop statement to another. If the original loop does not
     * possess an invariant, none is set to the target. A possibly existing old registration will be
     * overwritten, a registration for the original loop remains untouched.
     *
     * @param from the loop with the original contract
     * @param to the loop for which the contract is to be copied
     */
    public void copyLoopInvariant(LoopStatement from, LoopStatement to) {
        LoopSpecification inv = getLoopSpec(from);
        if (inv != null) {
            inv = inv.setLoop(to);
            addLoopInvariant(inv);
        }
    }

    /**
     * Registers the passed loop invariant, possibly overwriting an older registration for the same
     * loop.
     */
    public void addLoopInvariant(final LoopSpecification inv) {
        final LoopStatement loop = inv.getLoop();
        final int line = loop.getStartPosition().line();
        Pair<LoopStatement, Integer> l = new Pair<>(loop, line);
        loopInvs.put(l, inv);
        if (line != -1) {
            l = new Pair<>(loop, -1);
            loopInvs.put(l, inv);
        }
    }

    /**
     * Returns all block contracts for the specified block.
     *
     * @param block a block.
     * @return all block contracts for the specified block.
     */
    public ImmutableSet<BlockContract> getBlockContracts(StatementBlock block) {
        final Triple<StatementBlock, URI, Integer> b =
            new Triple<>(block, block.getParentClass(), block.getStartPosition().line());
        final ImmutableSet<BlockContract> contracts = blockContracts.get(b);
        if (contracts == null) {
            return DefaultImmutableSet.nil();
        } else {
            return contracts;
        }
    }

    /**
     * Returns all loop contracts for the specified block.
     *
     * @param block a block.
     * @return all loop contracts for the specified block.
     */
    public ImmutableSet<LoopContract> getLoopContracts(StatementBlock block) {
        final Triple<StatementBlock, URI, Integer> b =
            new Triple<>(block, block.getParentClass(), block.getStartPosition().line());
        final ImmutableSet<LoopContract> contracts = loopContracts.get(b);
        if (contracts == null) {
            return DefaultImmutableSet.nil();
        } else {
            return contracts;
        }
    }

    /**
     * Returns all loop contracts for the specified loop.
     *
     * @param loop a loop.
     * @return all loop contracts for the specified loop.
     */
    public ImmutableSet<LoopContract> getLoopContracts(LoopStatement loop) {
        final Pair<LoopStatement, Integer> b = new Pair<>(loop, loop.getStartPosition().line());
        final ImmutableSet<LoopContract> contracts = loopContractsOnLoops.get(b);
        if (contracts == null) {
            return DefaultImmutableSet.nil();
        } else {
            return contracts;
        }
    }

    public ImmutableSet<MergeContract> getMergeContracts(MergePointStatement mps) {
        final ImmutableSet<MergeContract> contracts = mergeContracts.get(mps);
        if (contracts == null) {
            return DefaultImmutableSet.nil();
        } else {
            return contracts;
        }
    }

    /**
     * Returns block contracts for according block statement and modality.
     *
     * @param block the given block.
     * @param modalityKind the given modality.
     */
    public ImmutableSet<BlockContract> getBlockContracts(final StatementBlock block,
            final Modality.JavaModalityKind modalityKind) {
        ImmutableSet<BlockContract> result = getBlockContracts(block);
        final Modality.JavaModalityKind matchModality = getMatchModalityKind(modalityKind);
        for (BlockContract contract : result) {
            if (!contract.getModalityKind().equals(matchModality) || (modalityKind.transaction()
                    && !contract.isTransactionApplicable() && !contract.isReadOnly(services))) {
                result = result.remove(contract);
            }
        }
        return result;
    }

    public ImmutableSet<LoopContract> getLoopContracts(final StatementBlock block,
            final Modality.JavaModalityKind modalityKind) {
        ImmutableSet<LoopContract> result = getLoopContracts(block);
        final Modality.JavaModalityKind matchModality = getMatchModalityKind(modalityKind);
        for (LoopContract contract : result) {
            if (!contract.getModalityKind().equals(matchModality) || (modalityKind.transaction()
                    && !contract.isTransactionApplicable() && !contract.isReadOnly(services))) {
                result = result.remove(contract);
            }
        }
        return result;
    }

    /**
     * Returns loop contracts for according loop statement and modality.
     *
     * @param loop the given loop.
     * @param modalityKind the given modality.
     * @return the set of resulting loop statements.
     */
    public ImmutableSet<LoopContract> getLoopContracts(final LoopStatement loop,
            final Modality.JavaModalityKind modalityKind) {
        ImmutableSet<LoopContract> result = getLoopContracts(loop);
        final Modality.JavaModalityKind matchModality = getMatchModalityKind(modalityKind);
        for (LoopContract contract : result) {
            if (!contract.getModalityKind().equals(matchModality) || (modalityKind.transaction()
                    && !contract.isTransactionApplicable() && !contract.isReadOnly(services))) {
                result = result.remove(contract);
            }
        }
        return result;
    }

    /**
     * Adds a new {@code BlockContract} and a new {@link FunctionalBlockContract} to the repository.
     *
     * @param contract the {@code BlockContract} to add.
     */
    public void addBlockContract(final BlockContract contract) {
        addBlockContract(contract, false);
    }

    /**
     * Adds a new {@code BlockContract} to the repository.
     *
     * @param contract the {@code BlockContract} to add.
     * @param addFunctionalContract whether or not to add a new {@link FunctionalBlockContract}
     *        based on {@code contract}.
     */
    public void addBlockContract(final BlockContract contract, boolean addFunctionalContract) {
        final StatementBlock block = contract.getBlock();
        final Triple<StatementBlock, URI, Integer> b =
            new Triple<>(block, block.getParentClass(), block.getStartPosition().line());
        blockContracts.put(b, getBlockContracts(block).add(contract));

        if (addFunctionalContract) {
            addContract(cf.funcBlock(contract));
        }
    }

    /**
     * <p>
     * Removes a {@code BlockContract} from the repository.
     * </p>
     *
     * <p>
     * The associated {@link FunctionalBlockContract} is not removed.
     * </p>
     *
     * @param contract the {@code BlockContract} to remove.
     */
    public void removeBlockContract(final BlockContract contract) {
        final StatementBlock block = contract.getBlock();
        final Triple<StatementBlock, URI, Integer> b =
            new Triple<>(block, block.getParentClass(), block.getStartPosition().line());

        ImmutableSet<BlockContract> set = blockContracts.get(b);
        blockContracts.put(b, set.remove(contract));
    }

    /**
     * Adds a new {@code LoopContract} and a new {@link FunctionalLoopContract} to the repository.
     *
     * @param contract the {@code LoopContract} to add.
     */
    public void addLoopContract(final LoopContract contract) {
        addLoopContract(contract, false);
    }

    /**
     * Adds a new {@code LoopContract} to the repository.
     *
     * @param contract the {@code LoopContract} to add.
     * @param addFunctionalContract whether or not to add a new {@link FunctionalLoopContract} based
     *        on {@code contract}.
     */
    public void addLoopContract(final LoopContract contract, boolean addFunctionalContract) {
        if (contract.isOnBlock()) {
            final StatementBlock block = contract.getBlock();
            final Triple<StatementBlock, URI, Integer> b =
                new Triple<>(block, block.getParentClass(), block.getStartPosition().line());
            loopContracts.put(b, getLoopContracts(block).add(contract));
        } else {
            final LoopStatement loop = contract.getLoop();
            final Pair<LoopStatement, Integer> b =
                new Pair<>(loop, loop.getStartPosition().line());
            loopContractsOnLoops.put(b, getLoopContracts(loop).add(contract));
        }

        if (addFunctionalContract) {
            if (contract.isInternalOnly()) {
                addContract(cf.funcBlock(contract.toBlockContract()));
            } else {
                addContract(cf.funcLoop(contract));
            }
        }
    }

    /**
     * <p>
     * Removes a {@code LoopContract} from the repository.
     * </p>
     *
     * <p>
     * The associated {@link FunctionalLoopContract} is not removed.
     * </p>
     *
     * @param contract the {@code LoopContract} to remove.
     */
    public void removeLoopContract(final LoopContract contract) {
        if (contract.isOnBlock()) {
            final StatementBlock block = contract.getBlock();
            final Triple<StatementBlock, URI, Integer> b =
                new Triple<>(block, block.getParentClass(), block.getStartPosition().line());

            ImmutableSet<LoopContract> set = loopContracts.get(b);
            loopContracts.put(b, set.remove(contract));
        } else {
            final LoopStatement loop = contract.getLoop();
            final Pair<LoopStatement, Integer> b =
                new Pair<>(loop, loop.getStartPosition().line());

            ImmutableSet<LoopContract> set = loopContractsOnLoops.get(b);
            loopContractsOnLoops.put(b, set.remove(contract));
        }
    }

    /**
     * Registers a {@link MergeContract}.
     *
     * @param mc The {@link MergeContract} to register.
     */
    public void addMergeContract(final MergeContract mc) {
        final MergePointStatement mps = mc.getMergePointStatement();
        mergeContracts.put(mps, getMergeContracts(mps).add(mc));
    }

    /**
     * Deletes the {@link MergeContract}s for a given {@link MergePointStatement}.
     *
     * @param mps The {@link MergePointStatement} to delete the registered contracts for.
     */
    public void removeMergeContracts(final MergePointStatement mps) {
        mergeContracts.put(mps, DefaultImmutableSet.nil());
    }

    public void addSpecs(ImmutableSet<SpecificationElement> specs) {
        for (SpecificationElement spec : specs) {
            if (spec instanceof Contract) {
                addContract((Contract) spec);
            } else if (spec instanceof ClassInvariant) {
                addClassInvariant((ClassInvariant) spec);
            } else if (spec instanceof InitiallyClause) {
                addInitiallyClause((InitiallyClause) spec);
            } else if (spec instanceof ClassAxiom) {
                addClassAxiom((ClassAxiom) spec);
            } else if (spec instanceof LoopSpecification) {
                addLoopInvariant((LoopSpecification) spec);
            } else if (spec instanceof BlockContract) {
                addBlockContract((BlockContract) spec);
            } else if (spec instanceof LoopContract) {
                addLoopContract((LoopContract) spec);
            } else if (spec instanceof MergeContract) {
                addMergeContract((MergeContract) spec);
            } else {
                assert false : "unexpected spec: " + spec + "\n(" + spec.getClass() + ")";
            }
        }
    }

    public Pair<IObserverFunction, ImmutableSet<Taclet>> limitObs(IObserverFunction obs) {
        assert limitedToUnlimited.get(obs) == null : " observer is already limited: " + obs;
        // TODO Was the exact class match "obs.getClass() !=
        // ObserverFunction.class" correctly converted into IProtramMethod?
        // Wojtek: I guess so, but why are IProgramMethods excluded from
        // limiting?
        // This kills limiting for model methods...
        // if(!(obs instanceof IObserverFunction && !(obs instanceof
        // IProgramMethod))) {
        // return null;
        // }

        IObserverFunction limited = unlimitedToLimited.get(obs);
        ImmutableSet<Taclet> taclets = unlimitedToLimitTaclets.get(obs);

        if (limited == null) {
            final String baseName =
                ((ProgramElementName) obs.name()).getProgramName() + LIMIT_SUFFIX;
            final Sort heapSort = services.getTypeConverter().getHeapLDT().targetSort();
            limited = new ObserverFunction(baseName, obs.sort(), obs.getType(), heapSort,
                obs.getContainerType(), obs.isStatic(), obs.getParamTypes(),
                obs.getHeapCount(services), obs.getStateCount());
            unlimitedToLimited.put(obs, limited);
            limitedToUnlimited.put(limited, obs);

            assert taclets == null;
            taclets = DefaultImmutableSet.<Taclet>nil()
                    .add(getLimitedToUnlimitedTaclet(limited, obs, services))
                    .add(getUnlimitedToLimitedTaclet(limited, obs, services));
            unlimitedToLimitTaclets.put(obs, taclets);
        }

        return new Pair<>(Objects.requireNonNull(limited), Objects.requireNonNull(taclets));
    }

    public IObserverFunction unlimitObs(IObserverFunction obs) {
        IObserverFunction result = limitedToUnlimited.get(obs);
        if (result == null) {
            result = obs;
        }
        return result;
    }

    // Public interface for well-definedness checks

    /**
     * Represent terms belong to model fields, so the well-definedness check considers both of them
     * together.
     *
     * @param kjt The relevant KeYJavaType
     */
    public void addRepresentsTermToWdChecksForModelFields(KeYJavaType kjt) {
        ImmutableSet<ClassAxiom> axs = axioms.get(kjt);
        if (axs == null) {
            return;
        }
        ImmutableSet<RepresentsAxiom> reps = DefaultImmutableSet.nil();
        for (ClassAxiom ax : axs) {
            if (ax instanceof RepresentsAxiom) {
                reps = reps.add((RepresentsAxiom) ax);
            }
        }
        final ProgramVariable heap = services.getTypeConverter().getHeapLDT().getHeap();
        for (RepresentsAxiom rep : reps) {
            boolean dep = false;
            for (MethodWellDefinedness ch : getWdMethodChecks(kjt)) {
                if (ch.modelField() && ch.getTarget().equals(rep.getTarget())) {
                    dep = true;
                    unregisterContract(ch);
                    Term represents = rep.getAxiom(heap, ch.getOrigVars().self, services);
                    WellDefinednessCheck newCh = ch.addRepresents(represents);
                    registerContract(newCh);
                }
            }
            if (!dep) {
                MethodWellDefinedness mwd = new MethodWellDefinedness(rep, services);
                registerContract(mwd);
            }
        }
    }

    /**
     * Registers a well-definedness check for a jml statement. It does not take care of its
     * visibility in the proof management dialog.
     *
     * @param swd The well-definedness check
     */
    public void addWdStatement(StatementWellDefinedness swd) {
        registerWdCheck(swd);
    }

    /**
     * Returns all registered well-definedness checks.
     */
    public ImmutableSet<WellDefinednessCheck> getAllWdChecks() {
        ImmutableSet<WellDefinednessCheck> result = DefaultImmutableSet.nil();
        for (ImmutableSet<WellDefinednessCheck> s : wdChecks.values()) {
            result = result.union(s);
        }
        return result;
    }


    // region Support SetStatement and JmlAssert
    private final Map<Statement, JmlStatementSpec> statementMap = new IdentityHashMap<>();

    public @Nullable JmlStatementSpec getStatementSpec(Statement statement) {
        return statementMap.get(statement);
    }

    public JmlStatementSpec addStatementSpec(Statement statement, JmlStatementSpec spec) {
        return statementMap.put(statement, spec);
    }

    /**
     * This record represents information which are necessary to evaluate JML statements.
     * JML statements need to maintain the current variable set as well as the updated information for the KeY terms
     * they describe. This record represents this information, i.e., the scope of variables, and a list of terms, in
     * an immutable fasion. Updates require to create instances.
     * <p>
     * <b>Note:</b> There is a immutability hole in {@link ProgramVariableCollection} due to mutable {@link Map}
     * <p>
     * For {@link de.uka.ilkd.key.java.statement.JmlAssert} this is the formula behind the assert.
     * For {@link de.uka.ilkd.key.java.statement.SetStatement} this is the target and the value terms.
     * You may want to use the index constant for accessing them:
     * {@link de.uka.ilkd.key.java.statement.SetStatement#INDEX_TARGET},
     * {@link de.uka.ilkd.key.java.statement.SetStatement#INDEX_VALUE},
     * {@link de.uka.ilkd.key.java.statement.JmlAssert#INDEX_CONDITION}
     *
     * @param vars
     * @param terms
     */
    public record JmlStatementSpec(
            ProgramVariableCollection vars,
            ImmutableList<Term> terms
    ){
        /**
         * Retrieve a term
         * @param index a index to the list of {@code terms}.
         * @return the term at {@code index} in the {@code terms} list
         * @throws IndexOutOfBoundsException if the given {@code index} is negative or {@code >= terms().size()}
         */
        public Term term(int index) {
            return terms.get(index);
        }

        /**
         * Retrieve a term with a update to the given {@code self} term.
         * @param services the corresponding services instance
         * @param self a term which describes the {@code self} object aka. this on the current sequence
         * @param index the index of the term in {@code terms()}
         * @return a term updated with {@code self} and the {@code vars()}.
         */
        public Term getTerm(Services services, Term self, int index) {
            var term = term(index);

            final TermFactory termFactory = services.getTermFactory();
            final TermReplacementMap replacementMap = new TermReplacementMap(termFactory);
            if (self != null) {
                replacementMap.replaceSelf(vars().selfVar, self, services);
            }
            replacementMap.replaceRemembranceLocalVariables(vars().atPreVars, vars().atPres, services);
            replacementMap.replaceRemembranceLocalVariables(vars().atBeforeVars, vars().atBefores, services);
            final OpReplacer replacer = new OpReplacer(replacementMap, termFactory, services.getProof());
            return replacer.replace(term);
        }

        /**
         * Updates the variables given the new {@code atPres} (variable in pre state) map and the services.
         * The update is applied directly and an updated specification is returned. You need to add
         * the updated spec to the statement in the {@link SpecificationRepository} by yourself.
         *
         * @param atPres a non-null map of a map of program variable to a term which describes
         *               the value of this variable in the pre-state.
         * @param services the corresponding services object
         * @return a fresh {@link JmlStatementSpec} instance, non-registered.
         */
        public JmlStatementSpec updateVariables(Map<LocationVariable, Term> atPres, Services services) {
            var termFactory = services.getTermFactory();
            var replacementMap = new TermReplacementMap(termFactory);
            replacementMap.replaceRemembranceLocalVariables(vars.atPreVars, atPres, services);
            var replacer = new OpReplacer(replacementMap, termFactory, services.getProof());
            var newTerms = terms().map(replacer::replace);
            return new JmlStatementSpec(
                    new ProgramVariableCollection(vars.selfVar, vars.paramVars, vars.resultVar, vars.excVar,
                            vars.atPreVars, atPres, vars.atBeforeVars, vars.atBefores),
                    newTerms);
        }
    }
    // endregion
}

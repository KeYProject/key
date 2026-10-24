/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.proof.mgt;

import java.util.*;
import java.util.Map.Entry;
import java.util.function.UnaryOperator;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.Statement;
import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.ast.declaration.ClassDeclaration;
import de.uka.ilkd.key.java.ast.declaration.ModifierKind;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.rule.RewriteTaclet;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.speclang.*;
import de.uka.ilkd.key.speclang.jml.JMLInfoExtractor;
import de.uka.ilkd.key.speclang.jml.translation.ProgramVariableCollection;
import de.uka.ilkd.key.speclang.translation.SLTranslationException;
import de.uka.ilkd.key.util.LimitedObservers;
import de.uka.ilkd.key.util.MiscTools;

import org.key_project.logic.Name;
import org.key_project.prover.sequent.Sequent;
import org.key_project.util.collection.*;

import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Central storage for all specification elements, such as contracts, class axioms, and loop
 * invariants. Provides methods for adding such elements to the repository, and for retrieving them
 * afterwards.
 */
public class SpecificationRepository {
    private static final Logger LOGGER = LoggerFactory.getLogger(SpecificationRepository.class);

    public static final String CONTRACT_COMBINATION_MARKER = "§";

    private final ContractFactory cf;

    protected final Map<Pair<KeYJavaType, IObserverFunction>, ImmutableSet<Contract>> contracts =
        new LinkedHashMap<>();
    protected final Map<Pair<KeYJavaType, IProgramMethod>, ImmutableSet<FunctionalOperationContract>> operationContracts =
        new LinkedHashMap<>();
    protected final Map<String, Contract> contractsByName = new LinkedHashMap<>();
    protected final Map<KeYJavaType, ImmutableSet<IObserverFunction>> contractTargets =
        new LinkedHashMap<>();
    private final Map<KeYJavaType, ImmutableSet<InitiallyClause>> initiallyClauses =
        new LinkedHashMap<>();

    protected final Services services;
    protected final TermBuilder tb;

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

    protected IObserverFunction getCanonicalFormForKJT(IObserverFunction obs, KeYJavaType kjt) {
        assert obs != null;
        assert kjt != null;
        if (!(obs instanceof IProgramMethod pm) || obs.getContainerType().equals(kjt)) {
            return LimitedObservers.unlimitObs(obs);
        }
        if (pm.isConstructor()) {
            assert pm.getContainerType().equals(kjt);
            return pm;
        }

        // search through all locally available methods
        final String name = pm.getMethodDeclaration().getName();
        final int numParams = pm.getParameterDeclarationCount();
        final List<IProgramMethod> candidatePMs =
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
        final var allSupertypes = services.getJavaInfo().getAllSupertypes(kjt);
        allSupertypes.remove(kjt);
        for (KeYJavaType sup : allSupertypes) {
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
        ImmutableList<Pair<KeYJavaType, IObserverFunction>> result = ImmutableList.nil();

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

    private Contract prepareContract(Contract contract) {        // sanity check
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

    protected void registerContract(Contract contract) {
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

    protected Contract registerContract(Contract contract,
            Pair<KeYJavaType, IObserverFunction> targetPair) {
        LOGGER.trace("Contract registered {}", contract);
        final KeYJavaType targetKJT = targetPair.first;
        final IObserverFunction targetMethod = targetPair.second;
        contract = contract.setTarget(targetKJT, targetMethod);
        final String name = contract.getName();
        if (contractsByName.get(name) != null) {
            LOGGER.error("Tried to add a contract with a non-unique name: {}", name);
            // throw new IllegalStateException("Tried to add a contract with a non-unique name: " +
            // name);
            return contract;
        }
        assert !name.contains(CONTRACT_COMBINATION_MARKER)
                : "Tried to add a contract with a name containing the" + " reserved character "
                    + CONTRACT_COMBINATION_MARKER + ": " + name;
        assert contract.id() != Contract.INVALID_ID : "Tried to add a contract with an invalid id!";
        contracts.put(targetPair, getContracts(targetKJT, targetMethod).add(contract));

        contractsByName.put(contract.getName(), contract);
        final ImmutableSet<IObserverFunction> oldTargets = getContractTargets(targetKJT);
        final ImmutableSet<IObserverFunction> newTargets = oldTargets.add(targetMethod);
        contractTargets.put(targetKJT, newTargets);

        // Special treatment
        if (contract instanceof FunctionalOperationContract operationContract) {
            operationContracts.put(new Pair<>(targetKJT, (IProgramMethod) targetMethod),
                getOperationContracts(targetKJT, (IProgramMethod) targetMethod)
                        .add(operationContract));
        }
        return contract;
    }

    /**
     * Removes the contract from the repository, but keeps its target.
     */
    protected void unregisterContract(Contract contract) {
        final KeYJavaType kjt = contract.getKJT();
        final Pair<KeYJavaType, IObserverFunction> tp = new Pair<>(kjt, contract.getTarget());
        contracts.put(tp, contracts.get(tp).remove(contract));
        if (contract instanceof FunctionalOperationContract) {
            final Pair<KeYJavaType, IProgramMethod> tp2 =
                new Pair<>(tp.first, (IProgramMethod) tp.second);
            operationContracts.put(tp2,
                operationContracts.get(tp2).remove((FunctionalOperationContract) contract));
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
                    // assert getContracts(kjt, pm).size() == (WellDefinednessCheck.isOn() ? 2 : 1)
                    // + oldContracts.size();
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
     * Helper for {@link #map(UnaryOperator, Services)}.
     *
     * @param map a map.
     * @param op an operator.
     * @param services services.
     */
    @SuppressWarnings("unchecked")
    protected <K, V extends SpecificationElement> void mapValueSets(Map<K, ImmutableSet<V>> map,
            UnaryOperator<JTerm> op, Services services) {
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

    // -------------------------------------------------------------------------
    // public interface
    // -------------------------------------------------------------------------

    // Thread-safety: a single SpecificationRepository is shared by all parallel-prover workers of a
    // proof. Most maps above are populated once during problem loading and then only read, so
    // concurrent reads of them are safe. The maps that are still *mutated during proving* -- the
    // lazy class-axiom memo (which now lives in the ClassAxiomComputer) and the contract maps --
    // are guarded by this object's monitor: every method that reads or writes one of them is
    // synchronized (a coarse lock). The monitor is reentrant, which is required because several of
    // these methods call one another (e.g. getClassAxioms recurses into enclosing classes,
    // addContract refreshes contractsByName). Lock ordering is one-way (this monitor -> JavaInfo's
    // cache lock via the services), so no deadlock arises.

    /**
     * Applies the specified operator to every contract in this repository.
     *
     * @param op an operator.
     * @param services services.
     * @see SpecificationElement#map(UnaryOperator, Services)
     */
    public synchronized void map(UnaryOperator<JTerm> op, Services services) {
        mapValueSets(contracts, op, services);
        mapValueSets(operationContracts, op, services);
        mapValueSets(initiallyClauses, op, services);
        // invariants and class axioms (incl. the memoized computed axiom sets) live in the
        // class-axiom computer now
        services.getClassAxiomComputer().map(op, services);
    }

    /**
     * Returns all registered contracts.
     */
    public ImmutableSet<Contract> getAllContracts() {
        ImmutableSet<Contract> result = DefaultImmutableSet.nil();
        for (ImmutableSet<Contract> s : contracts.values()) {
            result = result.union(s);
        }
        return result;
    }

    /**
     * Returns all registered (atomic) contracts for the passed target.
     */
    public ImmutableSet<Contract> getContracts(KeYJavaType kjt, IObserverFunction target) {
        target =
            getCanonicalFormForKJT(Objects.requireNonNull(target), Objects.requireNonNull(kjt));
        final Pair<KeYJavaType, IObserverFunction> pair = new Pair<>(kjt, target);
        final ImmutableSet<Contract> result = contracts.get(pair);
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
            IProgramMethod pm, JModality.JavaModalityKind modalityKind) {
        ImmutableSet<FunctionalOperationContract> result = getOperationContracts(kjt, pm);
        final boolean transactionModality =
            modalityKind.transaction();
        final JModality.JavaModalityKind matchModality = transactionModality
                ? ((modalityKind == JModality.JavaModalityKind.DIA_TRANSACTION)
                        ? JModality.JavaModalityKind.DIA
                        : JModality.JavaModalityKind.BOX)
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
    public @Nullable Contract getContractByName(String name) {
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
     * Adds postconditions raising from initially clauses to all constructors. <b>Warning</b>: To be
     * called after all contracts have been registered.
     *
     * @throws SLTranslationException may be thrown during contract extraction
     */
    public void createContractsFromInitiallyClauses() throws SLTranslationException {
        for (KeYJavaType kjt : initiallyClauses.keySet()) {
            for (InitiallyClause inv : initiallyClauses.get(kjt)) {
                createContractsFromInitiallyClause(inv, kjt);
                if (ModifierKind.allowsInheritance(inv.getVisibility())) {
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
     * Adds a new functional (auxiliary) contract to the repository that is derived from the given
     * {@code BlockContract}. The block contract itself is attached to its block by the caller.
     *
     * @param contract the {@code BlockContract} to add a functional contract for.
     */
    public void addFunctionalBlockContract(final BlockContract contract) {
        addContract(cf.funcBlock(contract));
    }

    /**
     * Adds a new functional (auxiliary) contract to the repository that is derived from the given
     * {@code LoopContract} (a functional loop contract, or a functional block contract if the loop
     * contract is only applicable internally). The loop contract itself is attached to its block or
     * loop by the caller.
     *
     * @param contract the {@code LoopContract} to add a functional contract for.
     */
    public void addFunctionalLoopContract(final LoopContract contract) {
        if (contract.isInternalOnly()) {
            addContract(cf.funcBlock(contract.toBlockContract()));
        } else {
            addContract(cf.funcLoop(contract));
        }
    }

    public void addSpecs(ImmutableSet<SpecificationElement> specs) {
        for (SpecificationElement spec : specs) {
            if (spec instanceof Contract) {
                addContract((Contract) spec);
            } else if (spec instanceof ClassInvariant) {
                services.getClassAxiomComputer().addClassInvariant((ClassInvariant) spec);
            } else if (spec instanceof InitiallyClause) {
                addInitiallyClause((InitiallyClause) spec);
            } else if (spec instanceof ClassAxiom) {
                services.getClassAxiomComputer().addClassAxiom((ClassAxiom) spec);
            } else if (spec instanceof LoopSpecification loopSpec) {
                loopSpec.getLoop().setLoopInvariant(loopSpec);
            } else if (spec instanceof BlockContract blockContract) {
                blockContract.getBlock().addBlockContract(blockContract);
            } else if (spec instanceof LoopContract loopContract) {
                if (loopContract.isOnBlock()) {
                    loopContract.getBlock().addLoopContract(loopContract);
                } else {
                    loopContract.getLoop().addLoopContract(loopContract);
                }
            } else if (spec instanceof MergeContract mergeContract) {
                mergeContract.getMergePointStatement().addMergeContract(mergeContract);
            } else {
                assert false : "unexpected spec: " + spec + "\n(" + spec.getClass() + ")";
            }
        }
    }

    // region Support SetStatement and JmlAssert
    // JmlAssert/SetStatement specs now live on the AST nodes themselves (JmlSpecCarrier):
    // no repository state is needed here anymore.

    /// Do what ever you want.
    /// Used by WD to modify/add represent clauses.
    public void processJavaType(KeYJavaType kjt) {
    }
    // endregion
}

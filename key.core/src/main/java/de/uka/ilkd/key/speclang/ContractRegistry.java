/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.speclang;

import java.util.Arrays;
import java.util.Comparator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Objects;
import java.util.function.UnaryOperator;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.JModality;
import de.uka.ilkd.key.util.LimitedObservers;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;
import org.key_project.util.collection.Pair;

import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * The per-node derived-spec cache for operation/dependency/block/loop contracts. This is the part
 * of the former {@code SpecificationRepository} that stored and indexed contracts: it owns the
 * contract maps ({@link #contracts}, {@link #operationContracts}, {@link #contractTargets},
 * {@link #contractsByName}), the contract id counters, and the helpers that resolve contract
 * overriding/inheritance and contract combination over the {@link JavaInfo}. (The initially
 * clauses that used to live here moved to {@link JMLSpecFactory} at load time.) It no longer
 * lives in the specification repository: it is owned by the {@link Services} of the environment
 * (shared by {@link Services#copy(boolean)} copies like the specification repository, the proof
 * registry and the class-axiom computer) and is fed by the load pipeline ({@code SLEnvInput},
 * {@code KeYFile}, {@link JMLSpecFactory}).
 *
 * <p>
 * The maps are keyed per node -- a {@code (KeYJavaType, IObserverFunction)} pair is the program
 * method (or observer) the contracts belong to -- which is why this cache is described as
 * "per-node". Contracts are still <em>derived</em> during loading by the specification extractors
 * and only cached here; the derivation itself happens in {@link JMLSpecFactory} and friends.
 * </p>
 *
 * <p>
 * Thread-safety: a single registry is shared by all parallel-prover workers of a proof. The maps
 * are populated once during problem loading and then only read, so concurrent reads are safe; the
 * maps that are mutated during proving (none today once loading finished, but the contract maps
 * and the initially-clause handling are written by {@link #addContract} etc.) are guarded by this
 * object's monitor (a coarse, reentrant lock -- several methods call one another).
 * </p>
 */
public class ContractRegistry {

    private static final Logger LOGGER = LoggerFactory.getLogger(ContractRegistry.class);

    private final ContractFactory cf;

    protected final Map<Pair<KeYJavaType, IObserverFunction>, ImmutableSet<Contract>> contracts =
        new java.util.LinkedHashMap<>();
    protected final Map<Pair<KeYJavaType, IProgramMethod>, ImmutableSet<FunctionalOperationContract>> operationContracts =
        new java.util.LinkedHashMap<>();
    protected final Map<String, Contract> contractsByName = new java.util.LinkedHashMap<>();
    protected final Map<KeYJavaType, ImmutableSet<IObserverFunction>> contractTargets =
        new java.util.LinkedHashMap<>();

    protected final Services services;
    protected final TermBuilder tb;

    private final Map<String, Integer> contractCounters =
        new de.uka.ilkd.key.util.LinkedHashMap<>();

    public ContractRegistry(Services services) {
        this.services = services;
        this.tb = services.getTermBuilder();
        cf = new ContractFactory(services);
    }

    // -------------------------------------------------------------------------
    // internal methods
    // -------------------------------------------------------------------------

    /**
     * Returns the canonical form of the passed observer function for the passed type: the
     * {@link IProgramMethod} locally declared in {@code kjt} that corresponds to {@code obs} by
     * name and parameter types (so contracts of inherited methods are reachable from the subtype),
     * or the unlimited observer otherwise.
     */
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

    /**
     * Returns all (type, method) pairs that override the passed target: the canonical forms of the
     * target in all subtypes of the target's type.
     */
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

    private Contract prepareContract(Contract contract) { // sanity check
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

    public void registerContract(Contract contract,
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
        assert !name.contains(ContractFactory.CONTRACT_COMBINATION_MARKER)
                : "Tried to add a contract with a name containing the" + " reserved character "
                    + ContractFactory.CONTRACT_COMBINATION_MARKER + ": " + name;
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
     * Removes the contract from the registry, but keeps its target.
     */
    public void unregisterContract(Contract contract) {
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

    // -------------------------------------------------------------------------
    // public interface
    // -------------------------------------------------------------------------

    /**
     * Applies the specified operator to every contract in this registry.
     *
     * @param op an operator.
     * @param services services.
     * @see SpecificationElement#map(UnaryOperator, Services)
     */
    public synchronized void map(UnaryOperator<JTerm> op, Services services) {
        mapValueSets(contracts, op, services);
        mapValueSets(operationContracts, op, services);
    }

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
        String[] baseNames = name.split(ContractFactory.CONTRACT_COMBINATION_MARKER);
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
            assert !contract.getName().contains(ContractFactory.CONTRACT_COMBINATION_MARKER)
                    : "Please combine only atomic contracts!";
        }

        // sort contracts alphabetically (for determinism)
        FunctionalOperationContract[] contractsArray =
            toCombine.toArray(new FunctionalOperationContract[toCombine.size()]);
        Arrays.sort(contractsArray,
            Comparator.comparing(SpecificationElement::getName));

        return cf.union(contractsArray);
    }

    /**
     * Splits the passed contract into its atomic components.
     */
    public ImmutableSet<Contract> splitContract(Contract contract) {
        ImmutableSet<Contract> result = DefaultImmutableSet.nil();
        String[] atomicNames =
            contract.getName().split(ContractFactory.CONTRACT_COMBINATION_MARKER);
        for (String atomicName : atomicNames) {
            Contract atomicContract = contractsByName.get(atomicName);
            if (atomicContract == null) {
                // This case happens in the symbolic execution debugger when
                // a temporary contract is used which is not part of the
                // specification repository
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
     * Adds a new functional (auxiliary) contract to the registry that is derived from the given
     * {@code BlockContract}. The block contract itself is attached to its block by the caller.
     *
     * @param contract the {@code BlockContract} to add a functional contract for.
     */
    public void addFunctionalBlockContract(final BlockContract contract) {
        addContract(cf.funcBlock(contract));
    }

    /**
     * Adds a new functional (auxiliary) contract to the registry that is derived from the given
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
}

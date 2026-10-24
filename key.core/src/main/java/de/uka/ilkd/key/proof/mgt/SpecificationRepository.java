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
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ContractPO;
import de.uka.ilkd.key.proof.init.ProofOblInput;
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
    private final Map<KeYJavaType, ImmutableSet<ClassInvariant>> invs = new LinkedHashMap<>();
    protected final Map<KeYJavaType, ImmutableSet<ClassAxiom>> axioms = new LinkedHashMap<>();
    private final Map<KeYJavaType, ImmutableSet<InitiallyClause>> initiallyClauses =
        new LinkedHashMap<>();
    private final Map<ProofOblInput, ImmutableSet<Proof>> proofs = new LinkedHashMap<>();

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
    // lazy allClassAxiomsCache, the limited/unlimited observer maps, and the contract maps -- are
    // guarded by this object's monitor: every method that reads or writes one of them is
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
        mapValueSets(invs, op, services);
        mapValueSets(axioms, op, services);
        mapValueSets(initiallyClauses, op, services);
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
     * Registers the passed class invariant, and inherits it to all subclasses if it is public or
     * protected.
     */
    public void addClassInvariant(ClassInvariant inv) {
        final KeYJavaType kjt = inv.getKJT();
        invs.put(kjt, getClassInvariants(kjt).add(inv));

        // in any case, create axiom with non-static target
        addClassAxiom(new PartialInvAxiom(inv, false, services));
        // for a static invariant, create also an axiom with a static target
        if (inv.isStatic()) {
            addClassAxiom(new PartialInvAxiom(inv, true, services));
        }
        // inherit non-private, non-static invariants
        if (!inv.isStatic() && ModifierKind.allowsInheritance(inv.getVisibility())) {
            final ImmutableList<KeYJavaType> subs = services.getJavaInfo().getAllSubtypes(kjt);
            for (KeYJavaType sub : subs) {
                ClassInvariant subInv = inv.setKJT(sub);
                invs.put(sub, getClassInvariants(sub).add(subInv));
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
     * Returns all class axioms visible in the passed class, including the axioms induced by
     * invariant declarations.
     */
    public synchronized ImmutableSet<ClassAxiom> getClassAxioms(KeYJavaType selfKjt) {
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
                final LocationVariable selfVar = tb.selfVar(kjt, false);

                JTerm invDef = tb.tt();
                JTerm staticInvDef = tb.tt();
                JTerm freeInvDef = tb.tt();
                JTerm freeStaticInvDef = tb.tt();

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
                        kjt, ModifierKind.PRIVATE, null, invDef, selfVar,
                        ImmutableList.nil(), null);
                result = result.add(invRepresentsAxiom);

                final ClassAxiom staticInvRepresentsAxiom = new RepresentsAxiom(
                    "Static class invariant axiom for " + kjt.getFullName(), staticInvSymbol, kjt,
                    ModifierKind.PRIVATE, null, staticInvDef, null, ImmutableList.nil(),
                    null);
                result = result.add(staticInvRepresentsAxiom);

                final ClassAxiom invFreeRepresentsAxiom = new RepresentsAxiom(
                    "Free class invariant axiom for " + kjt.getFullName(), freeInvSymbol, kjt,
                    ModifierKind.PRIVATE, null, freeInvDef, selfVar, ImmutableList.nil(),
                    null);
                result = result.add(invFreeRepresentsAxiom);

                final ClassAxiom staticFreeInvRepresentsAxiom = new RepresentsAxiom(
                    "Free static class invariant axiom for " + kjt.getFullName(),
                    freeStaticInvSymbol, kjt, ModifierKind.PRIVATE, null, freeStaticInvDef,
                    null,
                    ImmutableList.nil(), null);
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
                final LocationVariable selfVar = pm.isStatic() ? null : tb.selfVar(kjt, false);
                if (!pm.isVoid() && pm.isModel()) {
                    pm = services.getJavaInfo().getToplevelPM(kjt, pm);
                    ImmutableList<LocationVariable> paramVars = tb.paramVars(pm, false);
                    Map<LocationVariable, LocationVariable> atPreVars = new LinkedHashMap<>();
                    List<LocationVariable> heaps = HeapContext.getModifiableHeaps(services, false);
                    for (LocationVariable heap : heaps) {
                        atPreVars.put(heap,
                            tb.atPreVar(heap.name().toString(), heap.sort(), false));
                    }
                    LocationVariable resultVar = tb.resultVar(pm, false);

                    // This assumes there is one operation contract for each
                    // model pm per class
                    // We need to construct an inheritance chain of contracts
                    // starting at the bottom
                    ImmutableList<FunctionalOperationContract> lookupContracts =
                        ImmutableList.nil();
                    ImmutableSet<FunctionalOperationContract> cs = getOperationContracts(kjt, pm);
                    List<KeYJavaType> superTypes =
                        services.getJavaInfo().getAllSupertypes(kjt);
                    for (KeYJavaType superType : superTypes) {
                        for (FunctionalOperationContract fop : cs) {
                            if (fop.getSpecifiedIn().equals(superType)) {
                                lookupContracts = lookupContracts.append(fop);
                            }
                        }
                    }
                    for (FunctionalOperationContract fop : lookupContracts) {
                        JTerm representsFromContract = fop.getRepresentsAxiom(heaps.get(0), selfVar,
                            paramVars, tb.resultVar(pm, false), atPreVars, services);
                        JTerm preContract =
                            fop.getPre(heaps, selfVar, paramVars, atPreVars, services);
                        if (preContract == null) {
                            preContract = tb.tt();
                        }
                        if (representsFromContract != null) {
                            // TODO Wojtek: I do not understand the visibility
                            // issues of model fields/methods.
                            // Modifier visibility = pm.isPrivate() ?
                            // new Private() :
                            // (pm.isProtected() ? new Protected() :
                            // (pm.isPublic() ? new Public() : null));
                            final ClassAxiom modelMethodRepresentsAxiom =
                                new RepresentsAxiom(
                                    "Definition axiom for " + pm.getName() + " in "
                                        + kjt.getFullName(),
                                    pm, kjt, ModifierKind.PRIVATE, preContract,
                                    representsFromContract,
                                    selfVar, paramVars, atPreVars);
                            result = result.add(modelMethodRepresentsAxiom);
                            break;
                        }
                    }
                    for (FunctionalOperationContract fop : getOperationContracts(kjt, pm)) {
                        if (!fop.getSpecifiedIn().equals(kjt)) {
                            continue;
                        }
                        JTerm preFromContract =
                            fop.getPre(heaps, selfVar, paramVars, atPreVars, services);
                        JTerm freePreFromContract =
                            fop.getFreePre(heaps, selfVar, paramVars, atPreVars, services);
                        JTerm postFromContract = fop.getPost(heaps, selfVar, paramVars, resultVar,
                            null, atPreVars, services);
                        JTerm freePostFromContract = fop.getFreePost(heaps, selfVar, paramVars,
                            resultVar, null, atPreVars, services);
                        if (preFromContract != null
                                && ((postFromContract != null && postFromContract != tb.tt())
                                        || (freePostFromContract != null
                                                && freePostFromContract != tb.tt()))) {
                            JTerm mbyFromContract =
                                fop.hasMby() ? fop.getMby(selfVar, paramVars, services) : null;
                            final ClassAxiom modelMethodContractAxiom = new ContractAxiom(
                                "Contract axiom for " + pm.getName() + " in " + kjt.getFullName(),
                                pm,
                                kjt, ModifierKind.PRIVATE, preFromContract,
                                freePreFromContract,
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
     * Returns the class axioms declared in (registered for) the given type. This is the group among
     * which a {@link de.uka.ilkd.key.speclang.ClassAxiomImpl}'s taclet name must be unique; order
     * is
     * not significant.
     *
     * @param kjt the type
     * @return the axioms registered for {@code kjt}, or the empty set if none
     */
    public synchronized ImmutableSet<ClassAxiom> getClassAxiomsForType(KeYJavaType kjt) {
        final ImmutableSet<ClassAxiom> own = axioms.get(kjt);
        return own == null ? DefaultImmutableSet.nil() : own;
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
            if (ModifierKind.allowsInheritance(ax.getVisibility())) {
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
    public @Nullable ProofOblInput getProofOblInput(Proof proof) {
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
                addClassInvariant((ClassInvariant) spec);
            } else if (spec instanceof InitiallyClause) {
                addInitiallyClause((InitiallyClause) spec);
            } else if (spec instanceof ClassAxiom) {
                addClassAxiom((ClassAxiom) spec);
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

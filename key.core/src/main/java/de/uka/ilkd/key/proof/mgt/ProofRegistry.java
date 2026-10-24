/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.proof.mgt;

import java.util.LinkedHashMap;
import java.util.Map;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ContractPO;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.ContractFactory;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableSet;
import org.key_project.util.collection.Pair;

import org.jspecify.annotations.Nullable;

/**
 * Bidirectional registry between {@link ProofOblInput}s and the {@link Proof}s that were started
 * from them (the proof-to-PO bookkeeping that used to live in the {@code SpecificationRepository}
 * alongside the specification elements).
 *
 * <p>
 * The registry belongs to the *proof lifecycle*, not to JML: it is owned by the
 * {@link Services} of the environment a proof is performed in and shared by
 * {@link Services#copy(boolean)} copies (side proofs keep the same registry as their source
 * proof). This matters because several proof-loading paths register proofs through the shared
 * init-config {@link Services} without creating a {@link ProofEnvironment} in between.
 * </p>
 *
 * <p>
 * The map is keyed by the exact {@link ProofOblInput} a proof was started with. Lookups are
 * lenient on purpose: {@link #getProofs(ProofOblInput)} also returns the proofs of *stronger*
 * POs (those that {@link ProofOblInput#implies(Object) imply} the argument), and
 * {@link #getProofs(Contract)}/{@link #getProofs(KeYJavaType, IObserverFunction)} include
 * combined and overriding contracts. These semantics are preserved unchanged from the former
 * repository implementation.
 * </p>
 *
 * <p>
 * The contract-splitting and overriding-target resolution used by the contract-based lookups is
 * performed by the {@link de.uka.ilkd.key.speclang.ContractRegistry}; once the repository is
 * deleted, these helpers are already registry-owned.
 * </p>
 */
public class ProofRegistry {

    private final Services services;
    private final Map<ProofOblInput, ImmutableSet<Proof>> proofs = new LinkedHashMap<>();

    /**
     * Creates a registry for the given {@link Services}.
     *
     * @param services the services instance the registry belongs to.
     */
    public ProofRegistry(Services services) {
        this.services = services;
    }

    /**
     * Returns all proofs registered for the passed PO (or stronger POs).
     *
     * @param po the proof obligation input.
     * @return all registered proofs for the PO.
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
     * including the passed atomic contract.
     *
     * @param atomicContract the atomic contract.
     * @return all registered proofs for the contract.
     */
    public ImmutableSet<Proof> getProofs(Contract atomicContract) {
        assert !atomicContract.getName().contains(ContractFactory.CONTRACT_COMBINATION_MARKER)
                : "Contract must be atomic";

        ImmutableSet<Proof> result = DefaultImmutableSet.nil();
        for (Map.Entry<ProofOblInput, ImmutableSet<Proof>> entry : proofs.entrySet()) {
            final ProofOblInput po = entry.getKey();
            if (po instanceof ContractPO) {
                final Contract poContract = ((ContractPO) po).getContract();
                if (services.getContractRegistry().splitContract(poContract)
                        .contains(atomicContract)) {
                    result = result.union(entry.getValue());
                }
            }
        }
        return result;
    }

    /**
     * Returns all proofs registered for the passed target and its overriding targets.
     *
     * @param kjt the type of the target.
     * @param target the method target.
     * @return all registered proofs for the target(s).
     */
    public ImmutableSet<Proof> getProofs(KeYJavaType kjt, IObserverFunction target) {
        final ImmutableSet<Pair<KeYJavaType, IObserverFunction>> targets =
            services.getContractRegistry().getOverridingTargets(kjt, target)
                    .add(new Pair<>(kjt, target));
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
     * Returns all proofs registered with this registry.
     *
     * @return all registered proofs.
     */
    public ImmutableSet<Proof> getAllProofs() {
        ImmutableSet<Proof> result = DefaultImmutableSet.nil();
        for (ImmutableSet<Proof> proofSet : proofs.values()) {
            result = result.union(proofSet);
        }
        return result;
    }

    /**
     * Returns the PO that the passed proof is about, or {@code null}.
     *
     * @param proof the proof.
     * @return the contract PO, or {@code null}.
     */
    public @Nullable ContractPO getContractPOForProof(Proof proof) {
        ProofOblInput po = getProofOblInput(proof);
        if (po instanceof ContractPO) {
            return (ContractPO) po;
        } else {
            return null;
        }
    }

    /**
     * Returns the PO that the passed contract is about, or {@code null}.
     *
     * @param c the contract.
     * @return the contract PO, or {@code null}.
     */
    public @Nullable ContractPO getPO(Contract c) {
        for (ProofOblInput po : proofs.keySet()) {
            if (po instanceof ContractPO && ((ContractPO) po).getContract().equals(c)) {
                return (ContractPO) po;
            }
        }
        return null;
    }

    /**
     * Returns the contract PO that the passed proof is about, or {@code null}.
     *
     * @param proof the proof.
     * @return the contract PO, or {@code null}.
     */
    public @Nullable ContractPO getPOForProof(Proof proof) {
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
     * @param proof the proof.
     * @return the {@link ProofOblInput} of the given {@link Proof} or {@code null} if not
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
     * Returns the target that the passed proof is about, or {@code null}.
     *
     * @param proof the proof.
     * @return the target of the proof's contract PO, or {@code null}.
     */
    public @Nullable IObserverFunction getTargetOfProof(Proof proof) {
        final ContractPO po = getPOForProof(proof);
        return po == null ? null : po.getContract().getTarget();
    }

    /**
     * Registers the passed proof.
     *
     * @param po the proof obligation input.
     * @param proof the proof.
     */
    public void registerProof(ProofOblInput po, Proof proof) {
        proofs.put(po, getProofs(po).add(proof));
    }

    /**
     * Unregisters the passed proof.
     *
     * @param proof the proof.
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
}

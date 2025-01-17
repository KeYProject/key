/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.mgt;

import java.util.*;
import java.util.stream.Collectors;

import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofEvent;
import de.uka.ilkd.key.proof.RuleAppListener;
import de.uka.ilkd.key.proof.init.ContractPO;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;

import org.key_project.util.collection.ImmutableSet;

public class DependencyRepository {
    private final Map<IProgramMethod, Set<Contract>> method2Contracts = new HashMap<>();
    private final Map<Contract, Set<Contract>> dependencies = new HashMap<>();
    private final Map<DependencyArc, List<RuleJustification>> modifyingRuleApps = new HashMap<>();
    private final DefaultDepProofListener proofListener = new DefaultDepProofListener();

    public record DependencyArc(Contract from, Contract to) {}

    public DependencyRepository() {
    }

    public void registerContracts(SpecificationRepository specRepo) {
        specRepo.getAllContracts().forEach(c -> {
            if (c instanceof FunctionalOperationContract foc) {
                IProgramMethod target = foc.getTarget();
                if (target.getPositionInfo().getURI().map(uri -> uri.getScheme().equals("file"))
                        .orElse(false)) {
                    method2Contracts.computeIfAbsent(target, m -> new HashSet<>()).add(c);
                    dependencies.putIfAbsent(c, new HashSet<>());
                }
            }
        });
    }

    public void registerProof(Proof proof) {
        proof.addRuleAppListener(proofListener);
    }

    public Set<Contract> getDependencies(Contract from) {
        Set<Contract> inner = dependencies.get(from);
        if (inner == null) {
            return Collections.emptySet();
        }
        return Collections.unmodifiableSet(inner);
    }

    public Collection<Contract> getContractsWithDependencies() {
        return dependencies.entrySet().stream().filter(e -> !e.getValue().isEmpty())
                .map(Map.Entry::getKey).collect(Collectors.toList());
    }

    public void addDependency(Contract from, Contract to) {
        if (!dependencies.containsKey(from)) {
            throw new IllegalArgumentException(
                "Contract " + from.getName() + " is not registered!");
        }
        dependencies.get(from).add(to);
    }

    public void addDependency(Contract from, ImmutableSet<Contract> to, RuleJustification rj) {
        if (!dependencies.containsKey(from)) {
            throw new IllegalArgumentException(
                "Contract " + from.getName() + " is not registered!");
        }
        for (var c : to) {
            dependencies.get(from).add(c);
            modifyingRuleApps.computeIfAbsent(new DependencyArc(from, c), k -> new LinkedList<>())
                    .add(rj);
        }
    }

    public void removeDependency(Contract from, ImmutableSet<Contract> to, RuleJustification rj) {
        if (!dependencies.containsKey(from)) {
            throw new IllegalArgumentException(
                "Contract " + from.getName() + " is not registered!");
        }
        for (var c : to) {
            DependencyArc arc = new DependencyArc(from, c);
            var mra = modifyingRuleApps.get(arc);
            if (mra != null) {
                mra.remove(rj);
                if (mra.isEmpty()) {
                    dependencies.get(from).remove(c);
                    modifyingRuleApps.remove(arc);
                }
            }
        }
    }

    public void ruleApplied(RuleApp r, Proof proof) {
        RuleJustification rj =
            proof.getInitConfig().getJustifInfo().getJustification(r, proof.getServices());
        if (rj == null) {
            // LOGGER.debug("No justification found for rule " + r.rule().name());
            return;
        }
        if (!rj.isAxiomJustification()) {
            SpecificationRepository specRepo = proof.getServices().getSpecificationRepository();
            ContractPO cpo = specRepo.getContractPOForProof(proof);
            if (rj instanceof RuleJustificationBySpec(Contract spec)) {
                ImmutableSet<Contract> contracts = specRepo.splitContract(spec);
                ImmutableSet<Contract> to = specRepo.getInheritedContracts(contracts);
                addDependency(cpo.getContract(), to, rj);
            }
        }
    }

    public void ruleUnApplied(RuleApp r, Proof proof) {
        RuleJustification rj =
            proof.getInitConfig().getJustifInfo().getJustification(r, proof.getServices());
        if (rj == null) {
            // LOGGER.debug("No justification found for rule " + r.rule().name());
            return;
        }
        if (!rj.isAxiomJustification()) {
            SpecificationRepository specRepo = proof.getServices().getSpecificationRepository();
            ContractPO cpo = specRepo.getContractPOForProof(proof);
            if (rj instanceof RuleJustificationBySpec(Contract spec)) {
                ImmutableSet<Contract> contracts = specRepo.splitContract(spec);
                ImmutableSet<Contract> to = specRepo.getInheritedContracts(contracts);
                removeDependency(cpo.getContract(), to, rj);
            }
        }
    }

    private class DefaultDepProofListener implements RuleAppListener {
        public void ruleApplied(ProofEvent e) {
            DependencyRepository.this.ruleApplied(e.getRuleAppInfo().getRuleApp(), e.getSource());
        }
    }

    public void removeProofListener(Proof proof) {
        proof.removeRuleAppListener(proofListener);
        // proof.getServices().getProject().flushSingleProof(proof);
    }
}

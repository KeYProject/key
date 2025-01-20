/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.proof.mgt;

import java.util.LinkedHashMap;
import java.util.Map;

import org.key_project.rusty.Services;
import org.key_project.rusty.ast.expr.InfiniteLoopExpression;
import org.key_project.rusty.ast.expr.LoopExpression;
import org.key_project.rusty.logic.TermBuilder;
import org.key_project.rusty.logic.op.Modality;
import org.key_project.rusty.logic.op.ProgramFunction;
import org.key_project.rusty.speclang.Contract;
import org.key_project.rusty.speclang.FunctionalOperationContract;
import org.key_project.rusty.speclang.LoopSpecification;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableSet;

public class SpecificationRepository {
    private final Services services;
    private final TermBuilder tb;

    private final Map<ProgramFunction, ImmutableSet<Contract>> contracts = new LinkedHashMap<>();
    private final Map<ProgramFunction, ImmutableSet<FunctionalOperationContract>> operationContracts =
        new LinkedHashMap<>();
    private final Map<String, Contract> contractsByName = new LinkedHashMap<>();
    private final Map<String, Integer> contractCounters = new LinkedHashMap<>();
    private Map<LoopExpression, LoopSpecification> loopInvs = new LinkedHashMap<>();

    public SpecificationRepository(Services services) {
        this.services = services;
        tb = services.getTermBuilder();
    }

    public ImmutableSet<FunctionalOperationContract> getOperationContracts(ProgramFunction fn,
            Modality.RustyModalityKind modalityKind) {
        ImmutableSet<FunctionalOperationContract> result = getOperationContracts(fn);
        for (var contract : result) {
            if (!contract.getModalityKind().equals(modalityKind)) {
                result = result.remove(contract);
            }
        }
        return result;
    }

    private ImmutableSet<FunctionalOperationContract> getOperationContracts(ProgramFunction fn) {
        var result = operationContracts.get(fn);
        return result == null ? ImmutableSet.empty() : result;
    }

    /**
     * Returns all registered (atomic) contracts for the passed target.
     */
    public ImmutableSet<Contract> getContracts(ProgramFunction target) {
        final ImmutableSet<Contract> result = contracts.get(target);
        return result == null ? DefaultImmutableSet.nil() : result;
    }

    public void addContract(Contract contract) {
        contract = prepareContract(contract);
        registerContract(contract, (ProgramFunction) contract.getTarget());
    }

    private Contract prepareContract(Contract contract) {
        // set id
        Integer nextId = contractCounters.get(contract.getName());
        if (nextId == null) {
            nextId = 0;
        }
        contract = contract.setID(nextId);
        contractCounters.put(contract.getName(), nextId + 1);
        return contract;
    }

    private void registerContract(Contract contract, ProgramFunction target) {
        assert target != null;
        final String name = contract.getName();
        assert contractsByName.get(name) == null
                : "Tried to add a contract with a non-unique name: " + name;
        assert contract.id() != Contract.INVALID_ID : "Tried to add a contract with an invalid id!";
        contracts.put(target, getContracts(target).add(contract));
        if (contract instanceof FunctionalOperationContract foc) {
            operationContracts.put(target, getOperationContracts(target).add(foc));
        }
        contractsByName.put(name, contract);
    }

    /**
     * Returns the registered (atomic or combined) contract corresponding to the passed name, or
     * null.
     */
    public Contract getContractByName(String name) {
        if (name == null || name.isEmpty()) {
            return null;
        }
        return contractsByName.get(name);
    }

    /**
     * Returns the registered loop invariant for the passed loop, or null.
     */
    public LoopSpecification getLoopSpec(InfiniteLoopExpression loop) {
        // TODO: Java uses a pair of lines and loops. Why? Do we need that?
        return loopInvs.get(loop);
    }
}

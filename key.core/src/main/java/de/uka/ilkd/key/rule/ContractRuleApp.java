/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule;

import java.util.List;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.JModality;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;
import de.uka.ilkd.key.speclang.HeapContext;

import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;


/**
 * Represents an application of a contract rule. Currently, this is only used for applications read
 * in from a proof file; fresh applications are represented as regular BuiltInRuleApps. (yes, I know
 * that this is ugly - BW)
 */
@NullMarked
public class ContractRuleApp extends AbstractContractRuleApp<UseOperationContractRule> {
    private List<LocationVariable> heapContext;

    ContractRuleApp(UseOperationContractRule rule, @Nullable PosInOccurrence pio) {
        this(rule, pio, null);
    }

    private ContractRuleApp(UseOperationContractRule rule,
            @Nullable PosInOccurrence pio,
            @Nullable Contract instantiation) {
        super(rule, pio, instantiation);
    }

    public ContractRuleApp replacePos(PosInOccurrence newPos) {
        return new ContractRuleApp(rule(), newPos, instantiation);
    }

    public ContractRuleApp setContract(@Nullable Contract contract) {
        return new ContractRuleApp(rule(), posInOccurrence(), contract);
    }

    public UseOperationContractRule rule() {
        return super.rule();
    }

    public boolean isSufficientlyComplete() {
        return pio != null;
    }

    @Override
    public ContractRuleApp tryToInstantiate(Goal goal) {
        if (complete()) {
            return this;
        }
        Services services = goal.proof().getServices();
        ImmutableSet<FunctionalOperationContract> contracts =
            UseOperationContractRule.getApplicableContracts(
                UseOperationContractRule.computeInstantiation((JTerm) posInOccurrence().subTerm(),
                    services),
                services);
        if (contracts.size() != 1) {
            return this; // incomplete app;
        }
        var m = ((JModality) programTerm().op()).<JModality.JavaModalityKind>kind();
        heapContext = HeapContext.getModifiableHeaps(goal.proof().getServices(), m.transaction());
        return setContract(contracts.iterator().next());
    }

    @Override
    public ContractRuleApp forceInstantiate(Goal goal) {
        if (complete()) {
            return this;
        }
        Services services = goal.proof().getServices();
        ImmutableSet<FunctionalOperationContract> contracts =
            UseOperationContractRule.getApplicableContracts(UseOperationContractRule
                    .computeInstantiation((JTerm) posInOccurrence().subTerm(), services),
                services);
        var m = ((JModality) programTerm().op()).<JModality.JavaModalityKind>kind();
        heapContext = HeapContext.getModifiableHeaps(goal.proof().getServices(), m.transaction());
        final FunctionalOperationContract combinedContract =
            services.getSpecificationRepository().combineOperationContracts(contracts);
        return setContract(combinedContract);
    }

    @Override
    public ContractRuleApp setAssumesInsts(
            ImmutableList<PosInOccurrence> ifInsts) {
        super.setMutable(ifInsts);
        return this;
    }

    @Override
    public List<LocationVariable> getHeapContext() {
        return heapContext;
    }

    public JTerm programTerm() {
        if (posInOccurrence() != null) {
            return TermBuilder.goBelowUpdates((JTerm) posInOccurrence().subTerm());
        }
        return null;
    }

    @Override
    public IObserverFunction getObserverFunction(Services services) {
        return UseOperationContractRule.computeInstantiation((JTerm) posInOccurrence().subTerm(),
            services).pm();
    }

}

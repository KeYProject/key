/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.rule;

import org.key_project.logic.Term;
import org.key_project.rusty.Services;
import org.key_project.rusty.logic.PosInOccurrence;
import org.key_project.rusty.logic.TermBuilder;
import org.key_project.rusty.logic.op.IObserverFunction;
import org.key_project.rusty.logic.op.Modality;
import org.key_project.rusty.proof.Goal;
import org.key_project.rusty.speclang.Contract;
import org.key_project.rusty.speclang.FunctionalOperationContract;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;

/**
 * Represents an application of a contract rule. Currently, this is only used for applications read
 * in from a proof file; fresh applications are represented as regular BuiltInRuleApps. (yes, I know
 * that this is ugly - BW)
 */
public class ContractRuleApp extends AbstractContractRuleApp {
    ContractRuleApp(BuiltInRule rule, PosInOccurrence pio) {
        this(rule, pio, null);
    }

    private ContractRuleApp(BuiltInRule rule, PosInOccurrence pio, Contract instantiation) {
        super(rule, pio, instantiation);
    }

    public ContractRuleApp replacePos(PosInOccurrence newPos) {
        return new ContractRuleApp(rule(), newPos, instantiation);
    }

    public ContractRuleApp setContract(Contract contract) {
        return new ContractRuleApp(rule(), posInOccurrence(), contract);
    }

    public UseOperationContractRule rule() {
        return (UseOperationContractRule) super.rule();
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
            UseOperationContractRule.getApplicableContracts(UseOperationContractRule
                    .computeInstantiation(posInOccurrence().subTerm(), services),
                services);
        if (contracts.size() != 1) {
            return this; // incomplete app;
        }
        var m = ((Modality) programTerm().op()).<Modality.RustyModalityKind>kind();
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
                    .computeInstantiation(posInOccurrence().subTerm(), services),
                services);
        var m = ((Modality) programTerm().op()).<Modality.RustyModalityKind>kind();
        // final FunctionalOperationContract combinedContract =
        // services.getSpecificationRepository().combineOperationContracts(contracts);
        assert contracts.size() == 1;
        return setContract(contracts.iterator().next());
    }

    @Override
    public ContractRuleApp setIfInsts(ImmutableList<PosInOccurrence> ifInsts) {
        super.setMutable(ifInsts);
        return this;
    }

    public Term programTerm() {
        if (posInOccurrence() != null) {
            return TermBuilder.goBelowUpdates(posInOccurrence().subTerm());
        }
        return null;
    }

    @Override
    public IObserverFunction getObserverFunction(Services services) {
        return UseOperationContractRule.computeInstantiation(posInOccurrence().subTerm(),
            services).fn();
    }

}

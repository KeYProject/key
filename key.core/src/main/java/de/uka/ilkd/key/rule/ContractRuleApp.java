/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule;

import java.util.List;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;
import de.uka.ilkd.key.speclang.HeapContext;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;


/**
 * Represents an application of a contract rule. Currently, this is only used for applications read
 * in from a proof file; fresh applications are represented as regular BuiltInRuleApps. (yes, I know
 * that this is ugly - BW)
 */
public class ContractRuleApp extends AbstractContractRuleApp {

    private List<LocationVariable> heapContext;

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
        Modality m = (Modality) programTerm().op();
        boolean transaction = (m == Modality.DIA_TRANSACTION || m == Modality.BOX_TRANSACTION);
        heapContext = HeapContext.getModHeaps(goal.proof().getServices(), transaction);
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
        Modality m = (Modality) programTerm().op();
        boolean transaction = (m == Modality.DIA_TRANSACTION || m == Modality.BOX_TRANSACTION);
        heapContext = HeapContext.getModHeaps(goal.proof().getServices(), transaction);
        final FunctionalOperationContract combinedContract =
            services.getSpecificationRepository().combineOperationContracts(contracts);
        return setContract(combinedContract);
    }

    @Override
    public ContractRuleApp setIfInsts(ImmutableList<PosInOccurrence> ifInsts) {
        super.setMutable(ifInsts);
        return this;
    }

    @Override
    public List<LocationVariable> getHeapContext() {
        return heapContext;
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
            services).pm;
    }

}

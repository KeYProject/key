/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.rule.UseOperationContractRule;
import de.uka.ilkd.key.rule.UseOperationContractRule.Instantiation;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;

import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.util.collection.ImmutableSet;

import org.jspecify.annotations.NullMarked;

/**
 * This class completes the instantiation for a functional operation contract applications. The user
 * is queried for the contract to apply. If in forced mode the combined contracts will be used.
 */
@NullMarked
public class FunctionalOperationContractCompletion implements InteractiveRuleApplicationCompletion {

    @Override
    public IBuiltInRuleApp complete(IBuiltInRuleApp app, Goal goal, boolean forced) {
        Services services = goal.proof().getServices();

        if (forced) {
            app = app.forceInstantiate(goal);
            if (app.complete()) {
                return app;
            }
        }

        PosInOccurrence pio = app.posInOccurrence();
        if (pio == null) {
            // an operation-contract rule app always carries a position
            throw new NullPointerException("No position in occurrence available.");
        }
        Instantiation inst =
            UseOperationContractRule.computeInstantiation((JTerm) pio.subTerm(), services);
        if (inst == null) {
            // the rule always computes an instantiation for the application position
            throw new NullPointerException("No instantiation available.");
        }

        ImmutableSet<FunctionalOperationContract> contracts =
            UseOperationContractRule.getApplicableContracts(inst, services);

        FunctionalOperationContract[] contractsArr =
            contracts.toArray(new FunctionalOperationContract[contracts.size()]);

        ContractConfigurator cc = new ContractConfigurator(MainWindow.getInstance(), services,
            contractsArr, "Contracts for " + inst.pm().getName(), true);

        if (cc.wasSuccessful()) {
            Contract contract = cc.getContract();
            if (contract == null) {
                // a successful configuration always leaves a selected contract
                throw new NullPointerException("No contract selected.");
            }
            return ((UseOperationContractRule) app.rule())
                    .createApp(pio).setContract(contract);
        }
        return app;
    }

    @Override
    public boolean canComplete(IBuiltInRuleApp app) {
        return checkCanComplete(app);
    }

    /**
     * Checks if the app is supported. This functionality is also used by the Eclipse plug-ins like
     * the KeYIDE.
     */
    public static boolean checkCanComplete(final IBuiltInRuleApp app) {
        return app.rule() instanceof UseOperationContractRule;
    }
}

/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.contractcompletions;

import de.uka.ilkd.key.gui.fx.InteractiveRuleApplicationCompletionF;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.rule.UseOperationContractRule;
import de.uka.ilkd.key.rule.UseOperationContractRule.Instantiation;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;

import org.key_project.util.collection.ImmutableSet;

/**
 * contractcompletions (P2b): JavaFX port of the Swing
 * {@code FunctionalOperationContractCompletion} (FunctionalOperationContractCompletion.java,
 * 66 lines) — the interactive completion of a use operation contract application via the
 * {@link ContractConfiguratorF}. The logic is Swing-free; only the dialog differs.
 */
public class FunctionalOperationContractCompletionF
        implements InteractiveRuleApplicationCompletionF {

    @Override
    public IBuiltInRuleApp complete(IBuiltInRuleApp app, Goal goal, boolean forced) {
        Services services = goal.proof().getServices();

        if (forced) {
            app = app.forceInstantiate(goal);
            if (app.complete()) {
                return app;
            }
        }

        Instantiation inst = UseOperationContractRule
                .computeInstantiation((JTerm) app.posInOccurrence().subTerm(), services);

        ImmutableSet<FunctionalOperationContract> contracts =
            UseOperationContractRule.getApplicableContracts(inst, services);

        FunctionalOperationContract[] contractsArr =
            contracts.toArray(new FunctionalOperationContract[contracts.size()]);

        ContractConfiguratorF cc = new ContractConfiguratorF(services, contractsArr,
            "Contracts for " + inst.pm().getName(), true);
        cc.show();

        if (cc.wasSuccessful()) {
            return ((UseOperationContractRule) app.rule()).createApp(app.posInOccurrence())
                    .setContract(cc.getContract());
        }
        return app;
    }

    @Override
    public boolean canComplete(IBuiltInRuleApp app) {
        return checkCanComplete(app);
    }

    /** Swing {@code checkCanComplete} (also used by the KeY IDE). */
    public static boolean checkCanComplete(final IBuiltInRuleApp app) {
        return app.rule() instanceof UseOperationContractRule;
    }
}

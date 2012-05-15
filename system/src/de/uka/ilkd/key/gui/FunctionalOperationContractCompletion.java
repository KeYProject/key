package de.uka.ilkd.key.gui;

import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.rule.UseOperationContractRule;
import de.uka.ilkd.key.rule.UseOperationContractRule.Instantiation;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;


/**
 * This class completes the instantiation for a functional operation contract
 * applications. The user is queried for the contract to apply. If in forced mode the combined contracts 
 * will be used.
 */
public class FunctionalOperationContractCompletion implements InteractiveRuleApplicationCompletion {

    @Override
    public IBuiltInRuleApp complete(IBuiltInRuleApp app, Goal goal, boolean forced) {
        Services services = goal.proof().getServices();

        if (forced) {
            app = app.tryToInstantiate(goal);
            if (app.complete()) {
                return app;
            }
        }
        
        Instantiation inst = UseOperationContractRule.computeInstantiation(
                app.posInOccurrence().subTerm(), services);
        
        ImmutableSet<FunctionalOperationContract> contracts = UseOperationContractRule
                .getApplicableContracts(
                        inst, services);
        
        FunctionalOperationContract[] contractsArr = contracts
                .toArray(new FunctionalOperationContract[contracts.size()]);
        
        ContractConfigurator cc = new ContractConfigurator(
                MainWindow.getInstance(), services, contractsArr,
                "Contracts for " + inst.pm.getName(), true);
        
        if (cc.wasSuccessful()) {
            return  ((UseOperationContractRule) app.rule()).createApp(
                    app.posInOccurrence()).setContract(
                            cc.getContract());
        }
        return app;
    }

    @Override
    public boolean canComplete(IBuiltInRuleApp app) {
        return app.rule() instanceof UseOperationContractRule;
    }

}

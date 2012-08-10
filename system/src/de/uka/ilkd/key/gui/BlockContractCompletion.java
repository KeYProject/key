package de.uka.ilkd.key.gui;

import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.BlockContractRule;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.rule.BlockContractRule.Instantiation;
import de.uka.ilkd.key.speclang.BlockContract;

public class BlockContractCompletion implements InteractiveRuleApplicationCompletion {

	@Override
	public IBuiltInRuleApp complete(IBuiltInRuleApp application, Goal goal, boolean force) {
		Services services = goal.proof().getServices();
        if (force) {
            application = application.tryToInstantiate(goal);
            if (application.complete()) {
                return application;
            }
        }
        Instantiation instantiation = BlockContractRule.instantiate(application.posInOccurrence().subTerm(), services);
        ImmutableSet<BlockContract> contracts = BlockContractRule.getApplicableContracts(instantiation, services);
        ContractConfigurator configurator = new ContractConfigurator(
                MainWindow.getInstance(), services, contracts.toArray(new BlockContract[contracts.size()]),
                "Contracts for Block: " + instantiation.block, true);
        if (configurator.wasSuccessful()) {
            return  ((BlockContractRule) application.rule()).createApp(application.posInOccurrence()).setContract(configurator.getContract());
        }
        return application;
	}

	@Override
	public boolean canComplete(IBuiltInRuleApp app) {
		return app.rule() instanceof BlockContractRule;
	}

}
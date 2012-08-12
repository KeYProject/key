package de.uka.ilkd.key.gui;

import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.BlockContractBuiltInRuleApp;
import de.uka.ilkd.key.rule.BlockContractRule;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.rule.BlockContractRule.Instantiation;
import de.uka.ilkd.key.speclang.BlockContract;

// TODO Clean up.
public class BlockContractCompletion implements InteractiveRuleApplicationCompletion {

	@Override
	public IBuiltInRuleApp complete(final IBuiltInRuleApp application, final Goal goal, final boolean force)
    {
        IBuiltInRuleApp result = application;
		final Services services = goal.proof().getServices();
        if (force) {
            result = application.tryToInstantiate(goal);
            if (result.complete()) {
                return result;
            }
        }
        final Instantiation instantiation = BlockContractRule.instantiate(application.posInOccurrence().subTerm(), services);
        final ImmutableSet<BlockContract> contracts = BlockContractRule.getApplicableContracts(instantiation, services);
        final BlockContractConfigurator configurator = new BlockContractConfigurator(
            MainWindow.getInstance(), services, contracts.toArray(new BlockContract[contracts.size()]),
            "Contracts for Block: " + instantiation.block, true
        );
        if (configurator.wasSuccessful()) {
            return ((BlockContractBuiltInRuleApp) application.rule().createApp(application.posInOccurrence())).setContract(configurator.getContract(), goal);
        }
        return result;
	}

	@Override
	public boolean canComplete(final IBuiltInRuleApp app)
    {
		return app.rule() instanceof BlockContractRule;
	}

}
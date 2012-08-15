package de.uka.ilkd.key.gui;

import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.BlockContractBuiltInRuleApp;
import de.uka.ilkd.key.rule.BlockContractRule;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.rule.BlockContractRule.Instantiation;
import de.uka.ilkd.key.speclang.BlockContract;
import de.uka.ilkd.key.speclang.HeapContext;

import java.util.List;

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
        // TODO This is more or less exactly the code in BlockContractBuiltInRuleApp#tryToInstantiate.
        final Instantiation instantiation = BlockContractRule.instantiate(application.posInOccurrence().subTerm(), services);
        final ImmutableSet<BlockContract> contracts = BlockContractRule.getApplicableContracts(instantiation, services);
        final BlockContractConfigurator configurator = new BlockContractConfigurator(
            MainWindow.getInstance(), services, contracts.toArray(new BlockContract[contracts.size()]),
            "Contracts for Block: " + instantiation.block, true
        );
        if (configurator.wasSuccessful()) {
            final List<LocationVariable> heaps = HeapContext.getModHeaps(services, instantiation.transaction());
            return new BlockContractBuiltInRuleApp(application.rule(), application.posInOccurrence(), application.ifInsts(),
                                                   instantiation.block, configurator.getContract(), heaps);
        }
        return result;
	}

	@Override
	public boolean canComplete(final IBuiltInRuleApp app)
    {
		return app.rule() instanceof BlockContractRule;
	}

}
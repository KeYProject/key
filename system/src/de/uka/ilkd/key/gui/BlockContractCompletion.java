// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
//

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

public class BlockContractCompletion implements InteractiveRuleApplicationCompletion {

	@Override
	public IBuiltInRuleApp complete(final IBuiltInRuleApp application, final Goal goal, final boolean force)
    {
        BlockContractBuiltInRuleApp result = (BlockContractBuiltInRuleApp) application;
        if (!result.complete() && result.cannotComplete(goal)) {
            return result;
        }
        if (force) {
            result.tryToInstantiate(goal);
            if (result.complete()) {
                return result;
            }
        }
        final Services services = goal.proof().getServices();
        final Instantiation instantiation = BlockContractRule.instantiate(application.posInOccurrence().subTerm(), goal, services);
        final ImmutableSet<BlockContract> contracts = BlockContractRule.getApplicableContracts(instantiation, goal, services);
        final BlockContractConfigurator configurator = new BlockContractConfigurator(
            MainWindow.getInstance(), services, contracts.toArray(new BlockContract[contracts.size()]),
            "Contracts for Block: " + instantiation.block, true
        );
        if (configurator.wasSuccessful()) {
            final List<LocationVariable> heaps = HeapContext.getModHeaps(services, instantiation.isTransactional());
            result.update(instantiation.block, configurator.getContract(), heaps);
        }
        return result;
	}

	@Override
	public boolean canComplete(final IBuiltInRuleApp app)
    {
		return app.rule() instanceof BlockContractRule;
	}

}
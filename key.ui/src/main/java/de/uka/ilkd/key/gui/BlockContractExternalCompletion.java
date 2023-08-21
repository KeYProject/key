/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui;

import java.util.List;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.AbstractAuxiliaryContractRule.Instantiation;
import de.uka.ilkd.key.rule.BlockContractExternalBuiltInRuleApp;
import de.uka.ilkd.key.rule.BlockContractExternalRule;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.speclang.BlockContract;
import de.uka.ilkd.key.speclang.HeapContext;

import org.key_project.util.collection.ImmutableSet;

/**
 * Interactive completion for {@link BlockContractExternalBuiltInRuleApp}.
 */
public class BlockContractExternalCompletion implements InteractiveRuleApplicationCompletion {

    private final MainWindow mainWindow;

    BlockContractExternalCompletion(MainWindow mainWindow) {
        this.mainWindow = mainWindow;
    }

    @Override
    public IBuiltInRuleApp complete(final IBuiltInRuleApp application, final Goal goal,
            final boolean force) {
        BlockContractExternalBuiltInRuleApp result =
            (BlockContractExternalBuiltInRuleApp) application;
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
        final Instantiation instantiation = BlockContractExternalRule.INSTANCE
                .instantiate(application.posInOccurrence().subTerm(), goal, services);
        final ImmutableSet<BlockContract> contracts =
            BlockContractExternalRule.getApplicableContracts(instantiation, goal, services);
        final AuxiliaryContractConfigurator<BlockContract> configurator =
            new AuxiliaryContractConfigurator<>("Block Contract Configurator",
                new BlockContractSelectionPanel(services, true), mainWindow, services,
                contracts.toArray(new BlockContract[contracts.size()]),
                "Contracts for Block: " + instantiation.statement);
        if (configurator.wasSuccessful()) {
            final List<LocationVariable> heaps =
                HeapContext.getModHeaps(services, instantiation.isTransactional());
            result.update(instantiation.statement, configurator.getContract(),
                heaps);
        }
        return result;
    }

    @Override
    public boolean canComplete(final IBuiltInRuleApp app) {
        return checkCanComplete(app);
    }

    /**
     * Checks if the app is supported. This functionality is also used by the Eclipse plug-ins like
     * the KeYIDE.
     */
    public static boolean checkCanComplete(final IBuiltInRuleApp app) {
        return app.rule() instanceof BlockContractExternalRule;
    }
}

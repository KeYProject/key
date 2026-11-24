/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.contractcompletions;

import java.util.List;

import de.uka.ilkd.key.gui.fx.InteractiveRuleApplicationCompletionF;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.AbstractAuxiliaryContractRule.Instantiation;
import de.uka.ilkd.key.rule.BlockContractInternalBuiltInRuleApp;
import de.uka.ilkd.key.rule.BlockContractInternalRule;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.speclang.BlockContract;
import de.uka.ilkd.key.speclang.HeapContext;

import org.key_project.util.collection.ImmutableSet;

/**
 * contractcompletions (P2b): JavaFX port of the Swing {@code BlockContractInternalCompletion}
 * (BlockContractInternalCompletion.java, 78 lines) — the interactive completion of a block
 * contract (internal) application via {@link AuxiliaryContractConfiguratorF}. The logic is
 * Swing-free; only the dialog differs.
 */
public class BlockContractInternalCompletionF implements InteractiveRuleApplicationCompletionF {

    @Override
    public IBuiltInRuleApp complete(final IBuiltInRuleApp application, final Goal goal,
            final boolean force) {
        BlockContractInternalBuiltInRuleApp result =
            (BlockContractInternalBuiltInRuleApp) application;
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
        final Instantiation instantiation = BlockContractInternalRule.INSTANCE
                .instantiate((JTerm) application.posInOccurrence().subTerm(), goal);
        final ImmutableSet<BlockContract> contracts =
            BlockContractInternalRule.getApplicableContracts(instantiation, goal, services);
        final AuxiliaryContractConfiguratorF<BlockContract> configurator =
            new AuxiliaryContractConfiguratorF<>("Block Contract Configurator",
                new BlockContractSelectionPanelF(services, true), services,
                contracts.toArray(new BlockContract[contracts.size()]),
                "Contracts for Block: " + instantiation.statement());
        configurator.show();
        if (configurator.wasSuccessful()) {
            final List<LocationVariable> heaps =
                HeapContext.getModifiableHeaps(services, instantiation.isTransactional());
            result.update(instantiation.statement(), configurator.getContract(), heaps);
        }
        return result;
    }

    @Override
    public boolean canComplete(final IBuiltInRuleApp app) {
        return checkCanComplete(app);
    }

    /** Swing {@code checkCanComplete} (also used by the KeY IDE). */
    public static boolean checkCanComplete(final IBuiltInRuleApp app) {
        return app.rule() instanceof BlockContractInternalRule;
    }
}

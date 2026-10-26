/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui;

import java.util.List;

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

import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.util.collection.ImmutableSet;

import org.jspecify.annotations.NullMarked;

/**
 * Interactive completion of {@link BlockContractInternalBuiltInRuleApp}.
 */
@NullMarked
public class BlockContractInternalCompletion implements InteractiveRuleApplicationCompletion {

    private final MainWindow mainWindow;

    BlockContractInternalCompletion(MainWindow mainWindow) {
        this.mainWindow = mainWindow;
    }

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

        PosInOccurrence pio = application.posInOccurrence();
        if (pio == null) {
            // an interactive block-contract rule app always carries a position
            throw new NullPointerException("No position in occurrence available.");
        }
        final Instantiation instantiation =
            BlockContractInternalRule.INSTANCE.instantiate((JTerm) pio.subTerm(), goal);
        if (instantiation == null) {
            // the rule always instantiates the application position
            throw new NullPointerException("No instantiation available.");
        }
        final ImmutableSet<BlockContract> contracts =
            BlockContractInternalRule.getApplicableContracts(instantiation, goal, services);
        if (contracts == null) {
            // every block statement has at least the block contract of its program block
            throw new NullPointerException("No applicable contracts available.");
        }
        final AuxiliaryContractConfigurator<BlockContract> configurator =
            new AuxiliaryContractConfigurator<>("Block Contract Configurator",
                new BlockContractSelectionPanel(services, true), mainWindow, services,
                contracts.toArray(new BlockContract[contracts.size()]),
                "Contracts for Block: " + instantiation.statement());
        if (configurator.wasSuccessful()) {
            BlockContract blockContract = configurator.getContract();
            if (blockContract == null) {
                // a successful configuration always leaves a selected contract
                throw new NullPointerException("No block contract selected.");
            }
            final List<LocationVariable> heaps =
                HeapContext.getModifiableHeaps(services, instantiation.isTransactional());
            result.update(instantiation.statement(), blockContract, heaps);
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
        return app.rule() instanceof BlockContractInternalRule;
    }
}

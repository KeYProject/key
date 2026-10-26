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
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.rule.LoopContractInternalBuiltInRuleApp;
import de.uka.ilkd.key.rule.LoopContractInternalRule;
import de.uka.ilkd.key.speclang.HeapContext;
import de.uka.ilkd.key.speclang.LoopContract;

import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.util.collection.ImmutableSet;

import org.jspecify.annotations.NullMarked;

/**
 * Interactive completion for {@link LoopContractInternalBuiltInRuleApp}.
 */
@NullMarked
public class LoopContractInternalCompletion implements InteractiveRuleApplicationCompletion {

    private final MainWindow mainWindow;

    LoopContractInternalCompletion(MainWindow mainWindow) {
        this.mainWindow = mainWindow;
    }

    @Override
    public IBuiltInRuleApp complete(final IBuiltInRuleApp application, final Goal goal,
            final boolean force) {
        LoopContractInternalBuiltInRuleApp result =
            (LoopContractInternalBuiltInRuleApp) application;
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
            // an interactive loop-contract rule app always carries a position
            throw new NullPointerException("No position in occurrence available.");
        }
        final Instantiation instantiation =
            LoopContractInternalRule.INSTANCE.instantiate((JTerm) pio.subTerm(), goal);
        if (instantiation == null) {
            // the rule always instantiates the application position
            throw new NullPointerException("No instantiation available.");
        }
        final ImmutableSet<LoopContract> contracts =
            LoopContractInternalRule.INSTANCE
                    .getApplicableContracts(instantiation, goal, services);
        final AuxiliaryContractConfigurator<LoopContract> configurator =
            new AuxiliaryContractConfigurator<>("Loop Contract Configurator",
                new LoopContractSelectionPanel(services, true), mainWindow, services,
                contracts.toArray(new LoopContract[contracts.size()]),
                "Contracts for Block: " + instantiation.statement());
        if (configurator.wasSuccessful()) {
            LoopContract loopContract = configurator.getContract();
            if (loopContract == null) {
                // a successful configuration always leaves a selected contract
                throw new NullPointerException("No loop contract selected.");
            }
            final List<LocationVariable> heaps =
                HeapContext.getModifiableHeaps(services, instantiation.isTransactional());
            result.update(instantiation.statement(), loopContract, heaps);
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
        return app.rule() instanceof LoopContractInternalRule;
    }
}

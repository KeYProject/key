/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.macros;

import java.util.List;
import java.util.stream.Collectors;

import de.uka.ilkd.key.control.UserInterfaceControl;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.prover.impl.AutoProvers;

import org.key_project.prover.engine.GoalChooser;
import org.key_project.prover.engine.ProverCore;
import org.key_project.prover.engine.ProverTaskListener;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.util.collection.ImmutableList;

/**
 * The macro {@link DefaultAutoMacro} runs the active proof strategy on all enabled goals
 * in the selected subtree. This is equivalent to pressing the Auto button but can be
 * invoked from context menus or keyboard shortcuts.
 *
 * This is used to show traditional strategy application as an item in the context menus.
 *
 * @author mattias ulbrich
 */
public class DefaultAutoMacro extends AbstractProofMacro {

    @Override
    public String getName() {
        return "Full Automation";
    }

    @Override
    public String getCategory() {
        return "Auto Pilot";
    }

    @Override
    public String getScriptCommandName() {
        return "auto";
    }

    @Override
    public String getDescription() {
        return "<html>Runs the full proof strategy on the selected subtree.<br>" +
            "The strategy can be configured in 'Proof Search Strategy' tab.";
    }

    @Override
    public boolean canApplyTo(Proof proof, ImmutableList<Goal> goals,
            PosInOccurrence posInOcc) {
        return goals != null && !goals.isEmpty();
    }

    @Override
    public ProofMacroFinishedInfo applyTo(UserInterfaceControl uic, Proof proof,
            ImmutableList<Goal> goals, PosInOccurrence posInOcc, ProverTaskListener listener)
            throws InterruptedException {
        if (goals == null || goals.isEmpty()) {
            return null;
        }

        List<Node> nodes = goals.stream().map(Goal::node).collect(Collectors.toList());

        final GoalChooser goalChooser =
            proof.getInitConfig().getProfile().getSelectedGoalChooserBuilder().create();
        // Route through AutoProvers: this macro is the toolbar/context-menu equivalent of plain
        // automode, so it has to honour the selected prover mode (single- or multi-core).
        final ProverCore applyStrategy =
            AutoProvers.create(goalChooser, proof.getInitConfig().getProfile());

        final ProofMacroListener pml =
            new ProgressBarListener(1, getMaxSteps(proof), listener);
        applyStrategy.addProverTaskObserver(pml);

        try {
            applyStrategy.start(proof, goals);
            synchronized (applyStrategy) {
                if (applyStrategy.hasBeenInterrupted()) {
                    throw new InterruptedException();
                }
            }
        } finally {
            applyStrategy.removeProverTaskObserver(pml);
        }

        return new ProofMacroFinishedInfo(this, proof.openGoals(), nodes);
    }
}

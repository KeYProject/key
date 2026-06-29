/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.macros;


import de.uka.ilkd.key.control.UserInterfaceControl;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;

import org.key_project.prover.engine.ProverTaskListener;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.util.collection.ImmutableList;

/**
 * A proof macro that attempts to automatically close provable side branch goals.
 * <p>
 * This macro is a specialized variant of {@link TryCloseMacro} that focuses exclusively
 * on "easy" side goals that arise from exceptional execution paths, specifically:
 * </p>
 * <ul>
 * <li>Null reference exceptions</li>
 * <li>Index out of bounds exceptions</li>
 * </ul>
 * <p>
 * The macro traverses up the proof tree from each goal and identifies goals that belong
 * to side branches by examining node branch labels. Only goals on branches labeled with
 * "Null Reference" or "Index Out of Bounds" are processed.
 * </p>
 * <p>
 * This is useful for quickly discharging trivial exceptional cases while leaving the
 * main proof goals untouched for further manual or automated reasoning.
 * </p>
 * <p>
 * Accessible via the script command {@code "tryclose-sidebranches"}.
 * </p>
 *
 * @see TryCloseMacro
 */
public class TryCloseSideBranchesMacro extends TryCloseMacro {

    /**
     * Instantiates a new try close macro.
     * No changes to the max number of steps.
     */
    public TryCloseSideBranchesMacro() {
        super(-1);
    }

    /**
     * Instantiates a new try close macro.
     *
     * @param numberSteps
     *        the max number of steps. -1 means no change.
     */
    public TryCloseSideBranchesMacro(int numberSteps) {
        super(numberSteps);
    }

    @Override
    public String getName() {
        return "Close Provable Goals Below (Only side branches)";
    }

    @Override
    public String getScriptCommandName() {
        return "tryclose-sidebranches";
    }

    @Override
    public String getDescription() {
        return "Closes closable goals, leave rest untouched (see settings AutoPrune). " +
            "Applies only to supposedly easy side goals (null reference, index out of bounds) "
            + "beneath the selected node.";
    }

    @Override
    public ProofMacroFinishedInfo applyTo(UserInterfaceControl uic,
            Proof proof,
            ImmutableList<Goal> goals,
            PosInOccurrence posInOcc,
            ProverTaskListener listener) throws InterruptedException {
        ImmutableList<Goal> sideGoals = goals.filter(TryCloseSideBranchesMacro::isSideGoal);

        return super.applyTo(uic, proof, sideGoals, posInOcc, listener);
    }

    private static boolean isSideGoal(Goal g) {
        Node node = g.node();
        while (node != null && node.getNodeInfo() != null
                && node.getNodeInfo().getBranchLabel() != null) {
            String label = node.getNodeInfo().getBranchLabel();
            if (label.contains("Null Reference")
                    || label.contains("Index Out of Bounds")) {
                return true;
            }
            node = node.parent();
        }
        return false;
    }
}

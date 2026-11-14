/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.actions.useractions;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;

import org.key_project.prover.sequent.PosInOccurrence;

import org.jspecify.annotations.NullMarked;

/**
 * User action for "Apply rules automatically here" (i.e. focussed auto mode).
 *
 * @author Arne Keller
 */
@NullMarked
public class FocussedAutoModeUserAction extends ProofModifyingUserAction {
    /**
     * Focussed pio to apply rules on.
     */
    private final PosInOccurrence focus;

    /**
     * Construct a new focussed auto mode user action.
     *
     * @param mediator mediator
     * @param proof selected proof
     * @param focus formula to apply rules on
     */
    public FocussedAutoModeUserAction(KeYMediator mediator, Proof proof, PosInOccurrence focus) {
        super(mediator, proof);
        this.focus = focus;
    }

    @Override
    public String name() {
        return "Strategy: Focussed Auto Mode";
    }

    @Override
    protected void apply() {
        Goal selectedGoal = mediator.getSelectedGoal();
        if (selectedGoal == null) {
            // Focussed auto mode requires a goal; the action is only invoked while a goal is
            // selected, a {@code null} goal here is a concurrent state change in which the
            // previous code crashed with an NPE in the proof control.
            throw new NullPointerException("No goal selected for focussed auto mode.");
        }
        mediator.getUI().getProofControl().startFocussedAutoMode(
            focus, selectedGoal);
    }
}

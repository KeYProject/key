/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.actions.useractions;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Proof;

/**
 * User action for "Apply rules automatically here" (i.e. focussed auto mode).
 *
 * @author Arne Keller
 */
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
        mediator.getUI().getProofControl().startFocussedAutoMode(
            focus, mediator.getSelectedGoal());
    }
}

/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.exploration.actions;

import java.awt.event.ActionEvent;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.proof.Goal;

import org.key_project.exploration.ProofExplorationService;
import org.key_project.prover.sequent.PosInOccurrence;

import org.jspecify.annotations.NullMarked;

/**
 * Action for the user to visually delete formulas from the sequent (using hide)
 */
@NullMarked
public class DeleteFormulaAction extends ExplorationAction {

    private final PosInSequent posInSeq;

    public DeleteFormulaAction(PosInSequent pis) {
        this(pis, MainWindow.getInstance());
    }

    /**
     * The setter calls below happen on {@code this} while the receiver is still under
     * initialization (EISOP initialization check); safe here, suppressed with a scoped key.
     */
    @SuppressWarnings("nullness:method.invocation.invalid")
    public DeleteFormulaAction(PosInSequent pis, MainWindow mainWindow) {
        super(mainWindow);
        setName("Delete formula");
        this.posInSeq = pis;
        // only enable if position is in sequent and a toplevel formula
        PosInOccurrence pio = pis.getPosInOccurrence();
        if (pio != null) {
            setEnabled(!pis.isSequent() & pio.isTopLevel());
        } else {
            setEnabled(false);
        }
    }


    @Override
    public void actionPerformed(ActionEvent e) {
        PosInOccurrence pio = posInSeq.getPosInOccurrence();
        if (posInSeq.isSequent() || (pio != null && !pio.isTopLevel())) {
            return;
        }

        if (pio == null) {
            return;
        }
        JTerm term = (JTerm) pio.subTerm();
        Goal g = getMediator().getSelectedGoal();
        if (g == null) {
            throw new NullPointerException("No goal selected.");
        }
        ProofExplorationService service = ProofExplorationService.get(getMediator());
        service.soundHide(g, pio, term);
    }
}

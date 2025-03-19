/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.exploration.actions;

import java.awt.event.ActionEvent;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.proof.Goal;

import org.key_project.exploration.ProofExplorationService;

/**
 * Action for the user to visually delete formulas from the sequent (using hide)
 */
public class DeleteFormulaAction extends ExplorationAction {

    private final PosInSequent posInSeq;

    public DeleteFormulaAction(PosInSequent pis) {
        this(pis, MainWindow.getInstance());
    }

    public DeleteFormulaAction(PosInSequent pis, MainWindow mainWindow) {
        super(mainWindow);
        setName("Delete formula");
        this.posInSeq = pis;
        // only enable if position is in sequent and a toplevel formula
        if (pis.getPosInOccurrence() != null) {
            setEnabled(!pis.isSequent() & pis.getPosInOccurrence().isTopLevel());
        } else {
            setEnabled(false);
        }
    }


    @Override
    public void actionPerformed(ActionEvent e) {
        if (posInSeq.isSequent() || (posInSeq.getPosInOccurrence() != null
                && !posInSeq.getPosInOccurrence().isTopLevel())) {
            return;
        }

        PosInOccurrence pio = posInSeq.getPosInOccurrence();
        if (pio == null) {
            return;
        }
        Term term = pio.subTerm();
        Goal g = getMediator().getSelectedGoal();
        ProofExplorationService service = ProofExplorationService.get(getMediator());
        service.soundHide(g, pio, term);
    }
}

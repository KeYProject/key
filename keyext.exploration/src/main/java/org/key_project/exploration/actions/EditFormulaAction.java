/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.exploration.actions;

import java.awt.event.ActionEvent;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;

import org.key_project.exploration.ProofExplorationService;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.sequent.SequentFormula;

import org.jspecify.annotations.NullMarked;

/**
 * Action to edit formulas in the actions mode
 *
 * @author Alexander Weigl
 * @author Sarah Grebing
 * @version 2 (25.05.18)
 */
@NullMarked
public class EditFormulaAction extends ExplorationAction {
    private final transient PosInSequent posInSeq;

    public EditFormulaAction(PosInSequent pis) {
        this(pis, MainWindow.getInstance());
    }

    /**
     * The setter calls below happen on {@code this} while the receiver is still under
     * initialization (EISOP initialization check); safe here, suppressed with a scoped key.
     */
    @SuppressWarnings("nullness:method.invocation.invalid")
    public EditFormulaAction(PosInSequent pis, MainWindow mainWindow) {
        super(mainWindow);
        setName("Edit formula");
        this.posInSeq = pis;
        // enable only if position is in sequent
        setEnabled(!pis.isSequent());
    }

    /**
     * If action is chosen in context menu
     */
    @Override
    public void actionPerformed(ActionEvent e) {
        if (posInSeq.isSequent()) {
            return;
        }

        Services services = getMediator().getServices();
        if (services == null) {
            throw new NullPointerException("No services available.");
        }
        TermBuilder tb = services.getTermBuilder();
        PosInOccurrence pio = posInSeq.getPosInOccurrence();
        if (pio == null) {
            throw new NullPointerException("No formula position in the sequent.");
        }
        JTerm term = (JTerm) pio.subTerm();
        SequentFormula sf = pio.sequentFormula();
        Goal g = getMediator().getSelectedGoal();
        if (g == null) {
            throw new NullPointerException("No goal selected.");
        }
        JTerm newTerm = promptForTerm(mainWindow, term);
        if (newTerm == null) {
            throw new NullPointerException("No replacement term entered.");
        }

        if (newTerm.equals(term)) {
            return;
        }

        ProofExplorationService api = ProofExplorationService.get(getMediator());
        final JTerm formula = (JTerm) sf.formula();
        Node toBeSelected = api.applyChangeFormula(g, pio, formula,
            tb.replace(formula, pio.posInTerm(), newTerm));
        if (toBeSelected == null) {
            throw new NullPointerException("No node to be selected after the change.");
        }
        getMediator().getSelectionModel().setSelectedNode(toBeSelected);
    }
}

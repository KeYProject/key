/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.exploration.actions;

import java.awt.event.ActionEvent;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;

import org.key_project.exploration.ProofExplorationService;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.NullMarked;

/**
 * @author Alexander Weigl
 * @author Sarah Grebing
 * @version 1 (24.05.18)
 */
@NullMarked
public class AddFormulaToAntecedentAction extends ExplorationAction {
    public AddFormulaToAntecedentAction() {
        this(MainWindow.getInstance());
    }

    /**
     * The {@link #setName(String)} call happens on {@code this} while the receiver is still
     * under initialization (EISOP initialization check); safe here, suppressed with a scoped
     * key.
     */
    @SuppressWarnings("nullness:method.invocation.invalid")
    public AddFormulaToAntecedentAction(MainWindow mainWindow) {
        super(mainWindow);
        setName("Add formula to antecedent");
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        JTerm t = promptForTerm(mainWindow, null);
        if (t == null) {
            return;
        }
        ProofExplorationService service = ProofExplorationService.get(getMediator());
        Goal goal = getMediator().getSelectedGoal();
        if (goal == null) {
            throw new NullPointerException("No goal selected.");
        }
        @NonNull
        Node toBeSelected = service.soundAddition(goal, t, true);
        getMediator().getSelectionModel().setSelectedNode(toBeSelected);
    }
}

/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.exploration.actions;

import java.awt.event.ActionEvent;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Node;

import org.key_project.exploration.ProofExplorationService;

import org.jspecify.annotations.NonNull;

/**
 * @author Alexander Weigl
 * @author Sarah Grebing
 * @version 1 (24.05.18)
 */
public class AddFormulaToAntecedentAction extends ExplorationAction {
    public AddFormulaToAntecedentAction() {
        this(MainWindow.getInstance());
    }

    public AddFormulaToAntecedentAction(MainWindow mainWindow) {
        super(mainWindow);
        setName("Add formula to antecedent");
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        Term t = promptForTerm(mainWindow, null);
        if (t == null) {
            return;
        }
        ProofExplorationService service = ProofExplorationService.get(getMediator());
        @NonNull
        Node toBeSelected = service.soundAddition(getMediator().getSelectedGoal(), t, true);
        getMediator().getSelectionModel().setSelectedNode(toBeSelected);
    }
}

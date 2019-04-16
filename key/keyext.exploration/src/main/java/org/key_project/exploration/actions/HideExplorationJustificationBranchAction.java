package org.key_project.exploration.actions;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.MainWindowAction;
import de.uka.ilkd.key.gui.prooftree.GUIProofTreeModel;
import de.uka.ilkd.key.gui.prooftree.ProofTreeViewFilter;

import java.awt.event.ActionEvent;

public class HideExplorationJustificationBranchAction extends MainWindowAction {
    public HideExplorationJustificationBranchAction(MainWindow mainWindow) {
        super(mainWindow);
        this.setName("Hide Justification Branches");
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        GUIProofTreeModel delegateModel = mainWindow.getProofTreeView().getDelegateModel();
        delegateModel.setFilter(ProofTreeViewFilter.HIDE_CLOSED_SUBTREES, true);
    }
}

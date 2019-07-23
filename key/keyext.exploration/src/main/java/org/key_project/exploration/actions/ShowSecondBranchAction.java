package org.key_project.exploration.actions;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.KeyAction;
import org.key_project.exploration.ExplorationModeModel;
import org.key_project.exploration.Icons;

import java.awt.event.ActionEvent;

/**
 * @author Alexander Weigl
 * @version 1 (22.07.19)
 */
public class ShowSecondBranchAction extends KeyAction {
    private final ExplorationModeModel model;

    public ShowSecondBranchAction(ExplorationModeModel model) {
        this.model = model;
        setName("Show Justification Branch");
        setSelected(model.isShowSecondBranches());
        setTooltip("Exploration actions are \noften done using a cut. Choose to hide\n " +
                "the second cut-branches from the view \nto focus on the actions. Uncheck to focus on these branches.");
        setIcon(Icons.SECOND_BRANCH.get(24f));

        model.addPropertyChangeListener(ExplorationModeModel.PROP_SHOWSECONDBRANCH,
                e -> setSelected(model.isShowSecondBranches()));
        setSelected(model.isShowSecondBranches());
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        if (MainWindow.getInstance().getProofTreeView().getDelegateModel() == null) {
            // No proof loaded, so we cannot register the filter.
            return;
        }
        model.setShowSecondBranches(model.isShowSecondBranches());
        setSelected(model.isShowSecondBranches());
        if (model.isShowSecondBranches()) {
            model.setExplorationTacletAppState(ExplorationModeModel.ExplorationState.WHOLE_APP);
        } else {
            model.setExplorationTacletAppState(ExplorationModeModel.ExplorationState.SIMPLIFIED_APP);
        }
    }
}

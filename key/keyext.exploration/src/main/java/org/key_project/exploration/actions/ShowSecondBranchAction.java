package org.key_project.exploration.actions;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.KeyAction;
import org.key_project.exploration.ExplorationModeModel;
import org.key_project.exploration.Icons;

import javax.swing.*;
import java.awt.event.ActionEvent;

/**
 * @author Alexander Weigl
 * @version 1 (22.07.19)
 */
public class ShowSecondBranchAction extends KeyAction {
    private final transient ExplorationModeModel model;

    public ShowSecondBranchAction(ExplorationModeModel model) {
        this.model = model;
        setTooltip("Exploration actions are \noften done using a cut. Choose to hide\n " +
                "the second cut-branches from the view \nto focus on the actions. Uncheck to focus on these branches.");
        setMenuPath(ToggleExplorationAction.MENU_PATH);
        putValue(CHECKBOX, true);

        model.addPropertyChangeListener(ExplorationModeModel.PROP_SHOW_SECOND_BRANCH,
                e -> updateEnable());
        model.addPropertyChangeListener(ExplorationModeModel.PROP_EXPLORE_MODE, e -> updateEnable());
        updateEnable();
    }

    private void updateEnable() {
        setEnabled(model.isExplorationModeSelected());
        setSelected(model.isShowSecondBranches());
        setName(isSelected() ? "Hide justification" : "Show justification");

        Icon secondBranch;
        if(model.isShowSecondBranches()) {
            secondBranch = Icons.SECOND_BRANCH_HIDE.get(16);
        } else {
            secondBranch = Icons.SECOND_BRANCH;
        }
        setIcon(secondBranch);
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        if (MainWindow.getInstance().getProofTreeView().getDelegateModel() == null) {
            // No proof loaded, so we cannot register the filter.
            return;
        }
        boolean showSecondBranches = model.isShowSecondBranches();
        model.setShowSecondBranches(!showSecondBranches);
        setSelected(model.isShowSecondBranches());
        if (model.isShowSecondBranches()) {
            model.setExplorationTacletAppState(ExplorationModeModel.ExplorationState.WHOLE_APP);
        } else {
            model.setExplorationTacletAppState(ExplorationModeModel.ExplorationState.SIMPLIFIED_APP);
        }
        updateEnable();
    }
}

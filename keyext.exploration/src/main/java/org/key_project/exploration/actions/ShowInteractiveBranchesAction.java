/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.exploration.actions;

import java.awt.event.ActionEvent;
import javax.swing.*;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.KeyAction;
import de.uka.ilkd.key.settings.ProofIndependentSettings;

import org.key_project.exploration.ExplorationModeModel;
import org.key_project.exploration.Icons;

/**
 * @author Alexander Weigl
 * @version 1 (22.07.19)
 */
public class ShowInteractiveBranchesAction extends KeyAction {
    private final transient ExplorationModeModel model;

    public ShowInteractiveBranchesAction(ExplorationModeModel model, MainWindow mainWindow) {
        this.model = model;
        setName("Hide justification");
        setTooltip("Exploration actions are \noften done using a cut. Choose to hide\n "
            + "the second cut-branches from the view \nto focus on the actions. Uncheck to focus on these branches.");
        setMenuPath(ToggleExplorationAction.MENU_PATH);
        putValue(CHECKBOX, true);

        model.addPropertyChangeListener(ExplorationModeModel.PROP_EXPLORE_MODE,
            e -> updateEnable());
        ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings()
                .addPropertyChangeListener(e -> updateEnable());
        updateEnable();
    }

    private void updateEnable() {
        setSelected(!model.isShowInteractiveBranches());
        setEnabled(model.isExplorationModeSelected());

        Icon secondBranch;
        if (model.isShowInteractiveBranches()) {
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
        boolean showInteractiveBranches = model.isShowInteractiveBranches();
        model.setShowInteractiveBranches(!showInteractiveBranches);
        if (model.isShowInteractiveBranches()) {
            model.setExplorationTacletAppState(ExplorationModeModel.ExplorationState.WHOLE_APP);
        } else {
            model.setExplorationTacletAppState(
                ExplorationModeModel.ExplorationState.SIMPLIFIED_APP);
        }
    }
}

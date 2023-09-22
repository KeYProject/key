/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.exploration.actions;

import java.awt.event.ActionEvent;

import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.KeyAction;

import org.key_project.exploration.ExplorationModeModel;
import org.key_project.exploration.Icons;

/**
 * Toggles the Exploration Mode.
 *
 * @author Alexander Weigl
 * @version 1 (22.07.19)
 */
public class ToggleExplorationAction extends KeyAction {
    public static final String MENU_PATH = "View.Exploration";
    private final transient ExplorationModeModel model;

    public ToggleExplorationAction(ExplorationModeModel model, MainWindow mainWindow) {
        this.model = model;

        setName("Exploration Mode");
        setTooltip("Choose to start ExplorationMode");
        setIcon(Icons.EXPLORE.get());
        setSelected(model.isExplorationModeSelected());
        setMenuPath(MENU_PATH);
        putValue(CHECKBOX, true);
        model.addPropertyChangeListener(ExplorationModeModel.PROP_EXPLORE_MODE,
            e -> setSelected(model.isExplorationModeSelected()));

        mainWindow.getMediator().getSelectionModel()
                .addKeYSelectionListener(new KeYSelectionListener() {

                    @Override
                    public void selectedProofChanged(KeYSelectionEvent e) {
                        updateEnable(mainWindow);
                    }

                    @Override
                    public void selectedNodeChanged(KeYSelectionEvent e) {}
                });

        updateEnable(mainWindow);
    }

    private void updateEnable(MainWindow mainWindow) {
        // Only enable if a proof is loaded. Otherwise the buttons may become out of sync
        // with the actual settings which are loaded along with the proof.
        setEnabled(mainWindow.getProofTreeView().getDelegateModel() != null);
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        model.setExplorationModeSelected(!model.isExplorationModeSelected());
    }
}

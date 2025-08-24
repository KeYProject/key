/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.exploration.actions;

import java.awt.event.ActionEvent;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.MainWindowAction;

import org.key_project.exploration.ExplorationModeModel;
import org.key_project.exploration.Icons;

/**
 * Toggles the Exploration Mode.
 *
 * @author Alexander Weigl
 * @version 1 (22.07.19)
 */
public class ToggleExplorationAction extends MainWindowAction {
    public static final String MENU_PATH = "View.Exploration";
    private final transient ExplorationModeModel model;

    public ToggleExplorationAction(ExplorationModeModel model, MainWindow mainWindow) {
        super(mainWindow);
        this.model = model;

        setName("Exploration Mode");
        setTooltip("Choose to start ExplorationMode");
        setIcon(Icons.EXPLORE.get());
        setSelected(model.isExplorationModeSelected());
        setMenuPath(MENU_PATH);
        putValue(CHECKBOX, true);
        model.addPropertyChangeListener(ExplorationModeModel.PROP_EXPLORE_MODE,
            e -> setSelected(model.isExplorationModeSelected()));
        enabledOnAnActiveProof();
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        model.setExplorationModeSelected(!model.isExplorationModeSelected());
    }
}

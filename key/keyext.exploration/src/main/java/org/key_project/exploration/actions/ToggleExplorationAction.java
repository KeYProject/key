package org.key_project.exploration.actions;

import de.uka.ilkd.key.gui.actions.KeyAction;
import org.key_project.exploration.ExplorationModeModel;
import org.key_project.exploration.Icons;

import java.awt.event.ActionEvent;

/**
 * @author Alexander Weigl
 * @version 1 (22.07.19)
 */
public class ToggleExplorationAction extends KeyAction {
    public static final String MENU_PATH = "View.Exploration";
    private final ExplorationModeModel model;

    public ToggleExplorationAction(ExplorationModeModel model) {
        this.model = model;

        setName("Exploration Mode");
        setTooltip("Choose to start ExplorationMode");
        setIcon(Icons.EXPLORE.get());
        setSelected(model.isExplorationModeSelected());
        setMenuPath(MENU_PATH);
        putValue(CHECKBOX, true);
        model.addPropertyChangeListener(ExplorationModeModel.PROP_EXPLORE_MODE,
                e -> setSelected(model.isExplorationModeSelected()));
    }

    @Override
    public void actionPerformed(ActionEvent e) {

        boolean explorationModeSelected = model.isExplorationModeSelected();
        model.setExplorationModeSelected(!explorationModeSelected);
    }
}

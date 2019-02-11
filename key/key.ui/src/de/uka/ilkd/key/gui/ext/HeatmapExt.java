package de.uka.ilkd.key.gui.ext;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.HeatmapSettingsAction;
import de.uka.ilkd.key.gui.actions.HeatmapToggleAction;

import javax.swing.*;
import java.util.ArrayList;
import java.util.List;

/**
 * Extension adapter for Heatmap
 *
 * @author Alexander Weigl
 */
public class HeatmapExt implements KeYMainMenuExtension, KeYToolbarExtension {
    private List<Action> actions = new ArrayList<>(2);
    private HeatmapToggleAction toggleAction;
    private HeatmapSettingsAction settingsAction;

    @Override
    public List<Action> getMainMenuActions(MainWindow mainWindow) {
        return getActions(mainWindow);
    }

    private List<Action> getActions(MainWindow mainWindow) {
        if (actions.isEmpty()) {
            actions.add(toggleAction = new HeatmapToggleAction(mainWindow));
            actions.add(settingsAction = new HeatmapSettingsAction(mainWindow));
        }
        return actions;
    }

    @Override
    public int getPriority() {
        return 0;
    }

    @Override
    public JToolBar getToolbar(MainWindow mainWindow) {
        getActions(mainWindow);//initialize
        JToolBar tb = new JToolBar("Heatmap");
        JToggleButton comp = new JToggleButton(toggleAction);
        comp.setHideActionText(true);
        tb.add(comp);
        tb.add(settingsAction);
        return tb;
    }
}

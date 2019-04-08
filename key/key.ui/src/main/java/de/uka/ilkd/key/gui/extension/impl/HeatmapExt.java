package de.uka.ilkd.key.gui.extension.impl;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.HeatmapSettingsAction;
import de.uka.ilkd.key.gui.actions.HeatmapToggleAction;
import de.uka.ilkd.key.gui.extension.api.KeYGuiExtension;
import de.uka.ilkd.key.gui.settings.SettingsProvider;

import javax.swing.*;
import java.util.ArrayList;
import java.util.List;

/**
 * Extension adapter for Heatmap
 *
 * @author Alexander Weigl
 */
@KeYGuiExtension.Info(name = "Heatmap")
public class HeatmapExt implements KeYGuiExtension,
        KeYGuiExtension.MainMenu,
        KeYGuiExtension.Toolbar,
        KeYGuiExtension.Settings {
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
    public JToolBar getToolbar(MainWindow mainWindow) {
        getActions(mainWindow);//initialize
        JToolBar tb = new JToolBar("Heatmap");
        JToggleButton comp = new JToggleButton(toggleAction);
        comp.setHideActionText(true);
        tb.add(comp);
        tb.add(settingsAction);
        return tb;
    }

    @Override
    public SettingsProvider getSettings() {
        return new HeatmapSettingsProvider();
    }
}

class HeatmapSettingsProvider implements SettingsProvider {
    @Override
    public String getDescription() {
        return "Heatmap";
    }

    @Override
    public JComponent getPanel(MainWindow window) {
        return new JLabel("TODO");
    }

    @Override
    public void applySettings(MainWindow window) {
    }
}

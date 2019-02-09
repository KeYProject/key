package de.uka.ilkd.key.gui.ext;

import de.uka.ilkd.key.gui.HeatmapOptionsDialog;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.HeatmapSettingsAction;
import de.uka.ilkd.key.gui.actions.HeatmapToggleAction;

import javax.swing.*;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

public class HeatmapExt implements KeYMainMenu {
    @Override
    public List<Action> getActions(MainWindow mainWindow) {
        return Arrays.asList(
                new HeatmapToggleAction(mainWindow),
                new HeatmapSettingsAction(mainWindow)
        );
    }
}

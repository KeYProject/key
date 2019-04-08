package de.uka.ilkd.key.gui.settings;

import de.uka.ilkd.key.gui.IconFactory;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.KeyAction;
import de.uka.ilkd.key.gui.extension.ExtensionManager;
import de.uka.ilkd.key.gui.extension.impl.KeYGuiExtensionFacade;

import javax.swing.*;
import java.awt.event.ActionEvent;
import java.util.Comparator;
import java.util.LinkedList;
import java.util.List;

/**
 * @author Alexander Weigl
 * @version 1 (08.04.19)
 */
public class SettingsManager {
    private static SettingsManager INSTANCE;
    private List<SettingsProvider> settingsProviders = new LinkedList<>();

    static SettingsManager createWithExtensions() {
        SettingsManager sm = new SettingsManager();
        KeYGuiExtensionFacade.getSettingsProvider().forEach(it ->
                sm.settingsProviders.add(it.getSettings()));
        return sm;
    }

    public static SettingsManager getInstance() {
        if (INSTANCE == null) {
            INSTANCE = createWithExtensions();
            INSTANCE.add(new ExtensionManager());
        }
        return INSTANCE;
    }

    public void showSettingsDialog(MainWindow mainWindow) {
        settingsProviders.sort(Comparator.comparingInt(SettingsProvider::getPriorityOfSettings));
        SettingsDialog dialog = new SettingsDialog(mainWindow);
        dialog.setSettingsProvider(settingsProviders);
        dialog.setVisible(true);
    }

    public void showSettingsDialog(MainWindow mainWindow, SettingsProvider selectedPanel) {
        settingsProviders.sort(Comparator.comparingInt(SettingsProvider::getPriorityOfSettings));
        SettingsDialog dialog = new SettingsDialog(mainWindow);
        dialog.setSettingsProvider(settingsProviders);
        dialog.getUi().selectPanel(selectedPanel);
        dialog.setVisible(true);
    }

    public boolean add(SettingsProvider settingsProvider) {
        return settingsProviders.add(settingsProvider);
    }

    public boolean remove(SettingsProvider o) {
        return settingsProviders.remove(o);
    }

    public Action getActionShowSettings(MainWindow window) {
        class ShowSettingsAction extends KeyAction {
            public ShowSettingsAction() {
                setName("Show Settings");
                setIcon(IconFactory.editFile(16));
            }

            @Override
            public void actionPerformed(ActionEvent e) {
                showSettingsDialog(window);
            }
        }
        return new ShowSettingsAction();
    }
}

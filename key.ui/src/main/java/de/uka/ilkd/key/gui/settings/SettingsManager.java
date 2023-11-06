/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.settings;

import java.awt.event.ActionEvent;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.util.Comparator;
import java.util.LinkedList;
import java.util.List;
import java.util.Properties;
import javax.swing.*;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.MainWindowAction;
import de.uka.ilkd.key.gui.colors.ColorSettingsProvider;
import de.uka.ilkd.key.gui.extension.ExtensionManager;
import de.uka.ilkd.key.gui.extension.impl.KeYGuiExtensionFacade;
import de.uka.ilkd.key.gui.fonticons.IconFactory;
import de.uka.ilkd.key.gui.keyshortcuts.ShortcutSettings;
import de.uka.ilkd.key.gui.smt.settings.SMTSettingsProvider;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.settings.*;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * @author Alexander Weigl
 * @version 1 (08.04.19)
 */
public class SettingsManager {
    private static final Logger LOGGER = LoggerFactory.getLogger(SettingsManager.class);

    public static final ExtensionManager EXTENSION_MANAGER = new ExtensionManager();
    public static final SettingsProvider SMT_SETTINGS = new SMTSettingsProvider();
    public static final TacletOptionsSettings TACLET_OPTIONS_SETTINGS = new TacletOptionsSettings();
    public static final ShortcutSettings SHORTCUT_SETTINGS = new ShortcutSettings();
    public static final StandardUISettings STANDARD_UI_SETTINGS = new StandardUISettings();
    public static final ColorSettingsProvider COLOR_SETTINGS = new ColorSettingsProvider();

    private static SettingsManager INSTANCE;
    private final List<SettingsProvider> settingsProviders = new LinkedList<>();

    static SettingsManager createWithExtensions() {
        SettingsManager sm = new SettingsManager();
        KeYGuiExtensionFacade.getSettingsProvider()
                .forEach(it -> sm.settingsProviders.add(it.getSettings()));
        return sm;
    }

    public static SettingsManager getInstance() {
        if (INSTANCE == null) {
            INSTANCE = createWithExtensions();
            INSTANCE.add(STANDARD_UI_SETTINGS);
            // INSTANCE.add(SHORTCUT_SETTINGS);
            INSTANCE.add(SMT_SETTINGS);
            INSTANCE.add(EXTENSION_MANAGER);
            INSTANCE.add(TACLET_OPTIONS_SETTINGS);
            // INSTANCE.add(COLOR_SETTINGS);
        }
        return INSTANCE;
    }

    public static ProofDependentSMTSettings getSmtPdSettings(MainWindow window) {
        Proof proof = window.getMediator().getSelectedProof();
        ProofDependentSMTSettings pdSettings;
        if (proof == null) {
            return ProofSettings.DEFAULT_SETTINGS.getSMTSettings();
        } else {
            return proof.getSettings().getSMTSettings();
        }
    }

    public static NewSMTTranslationSettings getNewSmtSettings(MainWindow window) {
        Proof proof = window.getMediator().getSelectedProof();
        ProofDependentSMTSettings pdSettings;
        if (proof == null) {
            return ProofSettings.DEFAULT_SETTINGS.getNewSMTSettings();
        } else {
            return proof.getSettings().getNewSMTSettings();
        }
    }

    public static ProofIndependentSMTSettings getSmtPiSettings() {
        return ProofIndependentSettings.DEFAULT_INSTANCE.getSMTSettings();
    }

    public static ChoiceSettings getChoiceSettings(MainWindow window) {
        return ProofSettings.DEFAULT_SETTINGS.getChoiceSettings();
        /*
         * if (null != window.getMediator().getSelectedProof()) { return
         * window.getMediator().getSelectedProof().getSettings().getChoiceSettings(); } else {
         * return ProofSettings.DEFAULT_SETTINGS.getChoiceSettings(); }
         */
    }

    public static Properties loadProperties(File settingsFile) {
        Properties props = new Properties();
        if (settingsFile.exists()) {
            try (FileReader reader = new FileReader(settingsFile, StandardCharsets.UTF_8)) {
                props.load(reader);
            } catch (IOException e) {
                LOGGER.warn("Failed to load settings", e);
            }
        }
        return props;
    }

    public void showSettingsDialog(MainWindow mainWindow) {
        SettingsDialog dialog = createDialog(mainWindow);
        dialog.setVisible(true);
    }

    private SettingsDialog createDialog(MainWindow mainWindow) {
        settingsProviders.sort(Comparator.comparingInt(SettingsProvider::getPriorityOfSettings));
        initializeProviders(settingsProviders, mainWindow);

        SettingsDialog dialog = new SettingsDialog(mainWindow);
        dialog.setSettingsProvider(settingsProviders);
        dialog.setDefaultCloseOperation(WindowConstants.DISPOSE_ON_CLOSE);
        dialog.setIconImage(IconFactory.keyLogo());
        dialog.setLocationRelativeTo(mainWindow);
        return dialog;
    }

    /**
     * ensures that every given setting provider can update its model based on the current
     * mainWindow. This also includes the children of the settings.
     *
     * @param providers
     * @param mainWindow
     */
    private void initializeProviders(List<SettingsProvider> providers, MainWindow mainWindow) {
        providers.forEach(it -> it.getPanel(mainWindow));
        providers.forEach(it -> initializeProviders(it.getChildren(), mainWindow));
    }

    public void showSettingsDialog(MainWindow mainWindow, SettingsProvider selectedPanel) {
        SettingsDialog dialog = createDialog(mainWindow);
        dialog.getUi().selectPanel(selectedPanel);
        dialog.setVisible(true);
    }

    public boolean add(SettingsProvider settingsProvider) {
        return settingsProviders.add(settingsProvider);
    }

    public boolean remove(SettingsProvider o) {
        return settingsProviders.remove(o);
    }

    public class ShowSettingsAction extends MainWindowAction {
        private static final long serialVersionUID = 153753479823919818L;

        public ShowSettingsAction(MainWindow mainWindow) {
            super(mainWindow);
            setName("Show Settings");
            setIcon(IconFactory.editFile(16));
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            showSettingsDialog(mainWindow);
        }
    }

    public Action getActionShowSettings(MainWindow window) {
        return new ShowSettingsAction(window);
    }
}

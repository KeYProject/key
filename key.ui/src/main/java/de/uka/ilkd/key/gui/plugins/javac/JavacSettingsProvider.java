/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.plugins.javac;

import javax.swing.*;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.settings.SettingsPanel;
import de.uka.ilkd.key.gui.settings.SettingsProvider;
import de.uka.ilkd.key.settings.ProofIndependentSettings;

/**
 * Settings for the javac extension.
 *
 * @author Daniel Grévent
 */
public class JavacSettingsProvider extends SettingsPanel implements SettingsProvider {
    /**
     * Singleton instance of the slicing settings.
     */
    private static final JavacSettings JAVAC_SETTINGS = new JavacSettings();

    private static final String USE_CHECKERS_INFO = "If enabled the type checkers will be run in addition to the default java type checker.";
    private static final String CHECKERS_INFO = "The list of type checkers to run in addition to the default Java type checker. Each checkers should be written on a new line.";
    private static final String CHECKER_PATHS_INFO = "The list of paths to the type checkers and their dependencies. Each path should be absolute and be written on a new line.";

    private final JCheckBox useCheckers;
    private final JTextArea checkers;
    private final JTextArea paths;

    /**
     * Construct a new settings provider.
     */
    public JavacSettingsProvider() {
        useCheckers = addCheckBox(
                "use checkers", USE_CHECKERS_INFO, false, e -> {});
        checkers = addTextArea("checkers", "", CHECKERS_INFO, e -> {});
        paths = addTextArea("checker paths", "", CHECKER_PATHS_INFO, e -> {});

        setHeaderText("Javac Options");
    }

    @Override
    public String getDescription() {
        return "Java Type Checking";
    }

    public static JavacSettings getJavacSettings() {
        ProofIndependentSettings.DEFAULT_INSTANCE.addSettings(JAVAC_SETTINGS);
        return JAVAC_SETTINGS;
    }

    
    @Override
    public JPanel getPanel(MainWindow window) {
        JavacSettings settings = getJavacSettings();

        useCheckers.setSelected(settings.getUseCheckers());
        checkers.setText(settings.getCheckers());
        paths.setText(settings.getCheckerPaths());

        return this;
    }

    @Override
    public void applySettings(MainWindow window) {
        JavacSettings settings = getJavacSettings();

        settings.setUseCheckers(useCheckers.isSelected());
        settings.setCheckers(checkers.getText());
        settings.setCheckerPaths(paths.getText());
    }


    @Override
    public int getPriorityOfSettings() {
        return 10000;
    }
}

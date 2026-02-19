/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.plugins.javac;

import javax.swing.*;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.settings.SettingsPanel;
import de.uka.ilkd.key.gui.settings.SettingsProvider;
import de.uka.ilkd.key.settings.ProofIndependentSettings;

import net.miginfocom.layout.CC;

/**
 * Settings for the javac extension.
 *
 * @author Daniel Grévent
 */
public class JavacSettingsProvider extends SettingsPanel implements SettingsProvider {
    /**
     * Singleton instance of the javac settings.
     */
    private static final JavacSettings JAVAC_SETTINGS = new JavacSettings();

    /**
     * Text for the explanaition.
     */
    private static final String INTRO_LABEL =
        "This allows to run the Java compiler when loading Java files with additional processes such as Nullness or Ownership checkers.";

    /**
     * Information message for the {@link #useProcessors} checkbox.
     */
    private static final String USE_PROCESSORS_INFO =
        "If enabled the annotation processors will be run with the Java compiler while performing type checking of newly loaded sources.";

    /**
     * Information message for the {@link #processors} text area.
     */
    private static final String PROCESSORS_INFO = """
            A list of annotation processors to run while type checking with the Java compiler.
            Each checkers should be written on a new line.""";

    /**
     * Information message for the {@link #paths} text area.
     */
    private static final String CLASS_PATHS_INFO = """
            A list of additional class paths to be used by the Java compiler while type checking.
            These could for example be needed for certain annotation processors.
            Each path should be absolute and be written on a new line.""";

    private final JCheckBox useProcessors;
    private final JTextArea processors;
    private final JTextArea paths;

    /**
     * Construct a new settings provider.
     */
    public JavacSettingsProvider() {
        pCenter.add(new JLabel(INTRO_LABEL), new CC().span().alignX("left"));
        useProcessors = addCheckBox(
            "Enable Annotation Processing", USE_PROCESSORS_INFO, false, e -> {
            });
        processors = addTextArea("Annotation Processors", "", PROCESSORS_INFO, e -> {
        });
        paths = addTextArea("Processor Class Paths", "", CLASS_PATHS_INFO, e -> {
        });

        setHeaderText("Javac Options");
    }

    @Override
    public String getDescription() {
        return "Javac Options";
    }

    public static JavacSettings getJavacSettings() {
        ProofIndependentSettings.DEFAULT_INSTANCE.addSettings(JAVAC_SETTINGS);
        return JAVAC_SETTINGS;
    }


    @Override
    public JPanel getPanel(MainWindow window) {
        JavacSettings settings = getJavacSettings();

        useProcessors.setSelected(settings.getUseProcessors());
        processors.setText(settings.getProcessors());
        paths.setText(settings.getClassPaths());

        return this;
    }

    @Override
    public void applySettings(MainWindow window) {
        JavacSettings settings = getJavacSettings();

        settings.setUseProcessors(useProcessors.isSelected());
        settings.setProcessors(processors.getText());
        settings.setClassPaths(paths.getText());
    }


    @Override
    public int getPriorityOfSettings() {
        return 10000;
    }
}

/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.plugins.javac;

import javafx.scene.control.CheckBox;
import javafx.scene.control.Label;
import javafx.scene.control.TextArea;

import de.uka.ilkd.key.gui.fx.MainWindowF;
import de.uka.ilkd.key.gui.fx.settings.InvalidSettingsInputExceptionF;
import de.uka.ilkd.key.gui.fx.settings.SettingsPanelF;
import de.uka.ilkd.key.gui.fx.settings.SettingsProviderF;
import de.uka.ilkd.key.settings.ProofIndependentSettings;

/**
 * Settings for the javac extension.
 * <p>
 * FX port of the Swing {@code de.uka.ilkd.key.gui.plugins.javac.JavacSettingsProvider} ({@code
 * key.ui}, Daniel Grévent): a settings panel ({@code SettingsPanel} → here
 * {@link SettingsPanelF}) with the intro label, the <em>Enable Annotation Processing</em>
 * checkbox, and the <em>Annotation Processors</em> / <em>Processor Class Paths</em> text areas
 * ({@code JavacSettingsProvider.java:60-73}); the two text areas are enabled only while the
 * checkbox is selected ({@code :74-80}). {@code getPanel} re-reads the {@link JavacSettings},
 * {@code applySettings} writes them back ({@code :99-116}); the description is "Javac Options"
 * ({@code :64}) and the tree priority is 10000 ({@code :121}, sorted last like Swing).
 * <p>
 * <b>Plugins-package scope note:</b> the Swing {@code JavacExtension} contributes further
 * user-visible parts — the javac status-line widget with the compile feedback (via {@code
 * JavaCompilerCheckFacade}, {@code JavacExtension.java:110-141}) and the issue-list dialog
 * ({@code IssueDialog}, 877 Swing lines). These are deliberately deferred with the whole
 * {@code KeYGuiExtensionF} SPI (plan §6, M6): the FX status bar has no extension slot yet and
 * the compile pipeline requires a further {@code PositionedIssueString}/{@code
 * JavaCompilerCheckFacade} port. The settings tab is ported here as the extension-independent
 * user-visible part. Likewise the {@code action_history} plugin ({@code UndoHistoryButton} in
 * the toolbar) is deferred: its backend needs the Swing {@code UserActionListener} mediator API
 * ({@code key.ui}) that the FX mediator does not provide yet.
 */
public class JavacSettingsProviderF extends SettingsPanelF implements SettingsProviderF {

    /**
     * Singleton instance of the javac settings (Swing {@code JAVAC_SETTINGS}, registered into
     * {@code ProofIndependentSettings} on first use so it is persisted like in Swing).
     */
    private static final JavacSettings JAVAC_SETTINGS = new JavacSettings();

    /**
     * Text for the explanation (Swing {@code INTRO_LABEL}).
     */
    private static final String INTRO_LABEL =
        "This allows to run the Java compiler when loading Java files with additional "
            + "processes such as Nullness or Ownership checkers.";

    /**
     * Information message for the useProcessors checkbox (Swing {@code USE_PROCESSORS_INFO}).
     */
    private static final String USE_PROCESSORS_INFO =
        "If enabled the annotation processors will be run with the Java compiler while "
            + "performing type checking of newly loaded sources.";

    /**
     * Information message for the processors text area (Swing {@code PROCESSORS_INFO}).
     */
    private static final String PROCESSORS_INFO = """
            A list of annotation processors to run while type checking with the Java compiler.
            Each checkers should be written on a new line.""";

    /**
     * Information message for the paths text area (Swing {@code CLASS_PATHS_INFO}).
     */
    private static final String CLASS_PATHS_INFO = """
            A list of additional class paths to be used by the Java compiler while type checking.
            These could for example be needed for certain annotation processors.
            Each path should be absolute and be written on a new line.""";

    private final CheckBox useProcessors;
    private final TextArea processors;
    private final TextArea paths;

    /**
     * Construct a new settings provider (Swing constructor layout).
     */
    public JavacSettingsProviderF() {
        Label intro = new Label(INTRO_LABEL);
        intro.setWrapText(true);
        pCenter.add(intro, 0, pCenter.getRowCount(), 3, 1);
        processors = addTextArea("Annotation Processors", "", PROCESSORS_INFO, null, 4);
        paths = addTextArea("Processor Class Paths", "", CLASS_PATHS_INFO, null, 4);
        useProcessors = addCheckBox("Enable Annotation Processing", USE_PROCESSORS_INFO, false);
        // Swing ItemListener: the two text areas are disabled unless the checkbox is selected
        useProcessors.selectedProperty().addListener((obs, old, selected) -> {
            processors.setDisable(!selected);
            paths.setDisable(!selected);
        });
        processors.setDisable(!useProcessors.isSelected());
        paths.setDisable(!useProcessors.isSelected());

        setHeaderText("Javac Options");
    }

    /**
     * @return the (persisted) javac settings instance, registered like Swing
     *         {@code getJavacSettings()}
     */
    public static JavacSettings getJavacSettings() {
        ProofIndependentSettings.DEFAULT_INSTANCE.addSettings(JAVAC_SETTINGS);
        return JAVAC_SETTINGS;
    }

    @Override
    public String getDescription() {
        return "Javac Options";
    }

    @Override
    public javafx.scene.Node getPanel(MainWindowF window) {
        JavacSettings settings = getJavacSettings();

        // Swing getPanel: re-read the settings on every call (the panel is a singleton)
        useProcessors.setSelected(settings.getUseProcessors());
        processors.setText(settings.getProcessors());
        paths.setText(settings.getClassPaths());
        processors.setDisable(!useProcessors.isSelected());
        paths.setDisable(!useProcessors.isSelected());

        return this;
    }

    @Override
    public void apply(MainWindowF window) throws InvalidSettingsInputExceptionF {
        JavacSettings settings = getJavacSettings();

        // Swing applySettings: write the panel values back
        settings.setUseProcessors(useProcessors.isSelected());
        settings.setProcessors(processors.getText());
        settings.setClassPaths(paths.getText());
    }

    @Override
    public int getPriorityOfSettings() {
        return 10000;
    }

    /**
     * Self test of the provider (system property {@code key.fx.verify.javacsettings}, run at
     * startup from {@code MainWindowF}): reads/writes round trip through the panel — set test
     * values, read them back via {@link #getPanel(MainWindowF)}, change the panel controls and
     * write them back via {@link #apply(MainWindowF)} — and restores the previous values.
     *
     * @return a self-test report ending in {@code PASS} or {@code FAIL}
     */
    public static String verifyJavacSettings() {
        StringBuilder report = new StringBuilder("round-trip ");
        try {
            JavacSettings settings = getJavacSettings();
            // save and restore: the settings are shared with the running instance
            boolean oldUseProcessors = settings.getUseProcessors();
            String oldProcessors = settings.getProcessors();
            String oldClassPaths = settings.getClassPaths();
            try {
                settings.setUseProcessors(true);
                settings.setProcessors("verify.TestProcessor");
                settings.setClassPaths("/tmp/verify");

                // read path: getPanel loads the settings into the controls
                JavacSettingsProviderF panel = new JavacSettingsProviderF();
                panel.getPanel(null);
                boolean readOk = panel.useProcessors.isSelected()
                        && "verify.TestProcessor".equals(panel.processors.getText())
                        && "/tmp/verify".equals(panel.paths.getText())
                        && !panel.processors.isDisabled() && !panel.paths.isDisabled();
                report.append(readOk ? "read=ok; " : "read=FAIL; ");

                // write path: change the controls and apply
                panel.useProcessors.setSelected(false);
                panel.processors.setText("verify.OtherProcessor");
                panel.paths.setText("");
                try {
                    panel.apply(null);
                } catch (de.uka.ilkd.key.gui.fx.settings.InvalidSettingsInputExceptionF e) {
                    report.append("apply exception ").append(e).append("; ");
                }
                boolean writeOk = !settings.getUseProcessors()
                        && "verify.OtherProcessor".equals(settings.getProcessors())
                        && settings.getClassPaths().isEmpty();
                report.append(writeOk ? "write=ok; " : "write=FAIL; ");
            } finally {
                settings.setUseProcessors(oldUseProcessors);
                settings.setProcessors(oldProcessors);
                settings.setClassPaths(oldClassPaths);
            }
        } catch (RuntimeException e) {
            report.append("exception ").append(e).append("; ");
        }
        report.append(report.toString().contains("FAIL")
                || report.toString().contains("exception") ? "FAIL" : "PASS");
        return report.toString();
    }
}

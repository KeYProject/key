/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.isabelletranslation.fx;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Collection;
import java.util.List;
import javafx.scene.Node;
import javafx.scene.control.Label;
import javafx.scene.control.Spinner;
import javafx.scene.control.TextField;

import de.uka.ilkd.key.gui.fx.MainWindowF;
import de.uka.ilkd.key.gui.fx.settings.InvalidSettingsInputExceptionF;
import de.uka.ilkd.key.gui.fx.settings.SettingsPanelF;
import de.uka.ilkd.key.gui.fx.settings.SettingsProviderF;
import de.uka.ilkd.key.settings.Configuration;
import de.uka.ilkd.key.settings.PathConfig;

import org.key_project.isabelletranslation.IsabelleTranslationSettings;

import org.jspecify.annotations.NullMarked;

/**
 * The Isabelle translation settings panel, FX port of
 * {@code org.key_project.isabelletranslation.IsabelleSettingsProvider} (Swing
 * IsabelleSettingsProvider.java:27-211): the location of the translation files, the Isabelle
 * installation folder (with the live version-support check) and the solver timeout, reading and
 * writing the {@link IsabelleTranslationSettings} singleton
 * (IsabelleTranslationSettings.java:156-197).
 */
@NullMarked
final class IsabelleSettingsProviderF extends SettingsPanelF implements SettingsProviderF {

    private static final String INFO_TIMEOUT_FIELD =
        """
                Timeout for the external solvers in seconds.
                """;
    private static final String INFO_TRANSLATION_PATH_PANEL =
        """
                Choose where the isabelle translation files are stored.
                """;

    private static final Collection<String> SUPPORTED_VERSIONS_TEXT =
        List.of("Isabelle2023", "Isabelle2024-RC1", "Isabelle2024", "Isabelle2025");

    private static final String INFO_ISABELLE_PATH_PANEL = String.format(
        """
                Specify the absolute path of the Isabelle folder.
                %s.
                """, createSupportedVersionText());

    private enum IsabelleSupportState {
        SUPPORTED, NOT_SUPPORTED, NO_ISABELLE
    }

    /** Panel for inputting the path to where translations are stored */
    private final TextField translationPathPanel;

    /** Panel for inputting the path to Isabelle installation */
    private final TextField isabellePathPanel;

    /** Input field for timeout in seconds */
    private final Spinner<Integer> timeoutField;

    /** Supported version info for user */
    private final TextField versionSupported;

    /** The current settings object */
    private final IsabelleTranslationSettings settings;

    IsabelleSettingsProviderF() {
        setHeaderText(getDescription());
        setSubHeaderText("Isabelle settings are stored in: "
            // SETTINGS_FILE is package-protected in the keyext module; the public
            // PathConfig.getSettingsFile resolves the same file.
            + PathConfig.getSettingsFile("isabelleSettings.json").toAbsolutePath());
        this.settings = IsabelleTranslationSettings.getInstance();
        this.translationPathPanel = createTranslationPathPanel();
        this.isabellePathPanel = createIsabellePathPanel();
        this.timeoutField = createTimeoutField();
        createCheckSupportButton();
        this.versionSupported = createSolverSupported();
        updateVersionSupportText();
    }

    @Override
    public String getDescription() {
        return "Isabelle Translation";
    }

    @Override
    public Node getPanel(MainWindowF window) {
        // extension: MP9.3 — Swing IsabelleSettingsProvider.java:99-106: {@code getPanel} re-reads
        // the settings into the input components (panel instances are reused by the settings
        // dialog, so every open re-syncs).
        isabellePathPanel.setText(settings.getIsabellePath().toString());
        translationPathPanel.setText(settings.getTranslationPath().toString());
        timeoutField.getValueFactory().setValue(settings.getTimeout());
        return this;
    }

    private TextField createTranslationPathPanel() {
        return addFileChooserPanel("Location for translation files:", "",
            INFO_TRANSLATION_PATH_PANEL, false, null);
    }

    private TextField createIsabellePathPanel() {
        TextField panel = addFileChooserPanel("Isabelle installation folder:", "",
            INFO_ISABELLE_PATH_PANEL, false, null);
        // Swing IsabelleSettingsProvider.java:119-135: a DocumentListener re-checks the version
        // support while the path is being typed.
        panel.textProperty().addListener((obs, old, value) -> updateVersionSupportText());
        return panel;
    }

    private Spinner<Integer> createTimeoutField() {
        Spinner<Integer> spinner =
            addIntNumberField("Timeout:", 1, Integer.MAX_VALUE, 1, settings.getTimeout(),
                INFO_TIMEOUT_FIELD, null);
        // Swing IsabelleSettingsProvider.java:142-150 keeps a ChangeListener on the JSpinner that
        // writes the timeout immediately (the Swing applySettings does not persist it itself —
        // IsabelleTranslationSettings.java:175-190 falls back to the default 30 when the key is
        // absent).
        spinner.valueProperty().addListener((obs, old, value) -> {
            if (value != null) {
                settings.setTimeout(value);
            }
        });
        return spinner;
    }

    private void createCheckSupportButton() {
        javafx.scene.control.Button checkForSupportButton =
            new javafx.scene.control.Button("Check for support");
        checkForSupportButton.setOnAction(e -> updateVersionSupportText());
        addRowWithHelp(null, new Label(), checkForSupportButton);
    }

    private void updateVersionSupportText() {
        versionSupported.setText(getSolverSupportText());
    }

    private IsabelleSupportState checkForSupport() {
        String isabelleVersion;
        Path isabelleIdentifierPath =
            Paths.get(isabellePathPanel.getText(), "/etc/ISABELLE_IDENTIFIER");
        try {
            isabelleVersion = Files.readAllLines(isabelleIdentifierPath).getFirst();
        } catch (IOException e) {
            return IsabelleSupportState.NO_ISABELLE;
        }
        return SUPPORTED_VERSIONS_TEXT.contains(isabelleVersion) ? IsabelleSupportState.SUPPORTED
                : IsabelleSupportState.NOT_SUPPORTED;
    }

    private TextField createSolverSupported() {
        TextField txt = addTextField("Support", getSolverSupportText(),
            createSupportedVersionText(), null);
        txt.setEditable(false);
        return txt;
    }

    private static String createSupportedVersionText() {
        return "Supports these Isabelle versions: " + String.join(", ", SUPPORTED_VERSIONS_TEXT);
    }

    private String getSolverSupportText() {
        return switch (checkForSupport()) {
            case NOT_SUPPORTED ->
                "This version of Isabelle is not supported and is thus unlikely to work.";
            case SUPPORTED -> "This version of Isabelle is supported.";
            case NO_ISABELLE -> "Isabelle could not be found in the chosen directory.";
        };
    }

    @Override
    public void apply(MainWindowF window) throws InvalidSettingsInputExceptionF {
        // extension: MP9.3 — Swing IsabelleSettingsProvider.java:204-211: {@code applySettings}
        // writes a fresh Configuration and lets the settings object read it back (this triggers
        // the session-file creation of IsabelleTranslationSettings when the translation path
        // changed, IsabelleTranslationSettings.java:182-187). Unlike the Swing original the
        // timeout is carried in the Configuration as well, so applying the panel cannot reset it
        // to the default 30.
        Configuration newConfig = new Configuration();
        // KNOWN-SIMPLIFIED: the key constants (isabellePathKey / translationPathKey / timeoutKey)
        // are package-protected in the keyext module; their stable string values are mirrored here.
        newConfig.set("Path", isabellePathPanel.getText());
        newConfig.set("TranslationPath", translationPathPanel.getText());
        newConfig.set("Timeout", String.valueOf(timeoutField.getValue()));
        settings.readSettings(newConfig);
        updateVersionSupportText();
    }
}

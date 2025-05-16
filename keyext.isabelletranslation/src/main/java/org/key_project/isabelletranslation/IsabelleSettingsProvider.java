/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.isabelletranslation;

import java.io.IOException;
import java.math.RoundingMode;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Collection;
import java.util.List;
import javax.swing.*;
import javax.swing.event.DocumentEvent;
import javax.swing.event.DocumentListener;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.settings.InvalidSettingsInputException;
import de.uka.ilkd.key.gui.settings.SettingsPanel;
import de.uka.ilkd.key.gui.settings.SettingsProvider;
import de.uka.ilkd.key.settings.Configuration;

/**
 * {@link SettingsProvider} for Isabelle translation extension
 */
public class IsabelleSettingsProvider extends SettingsPanel implements SettingsProvider {
    private static final String INFO_TIMEOUT_FIELD =
        """
                Timeout for the external solvers in seconds.
                """;
    private static final String infoTranslationPathPanel =
        """
                Choose where the isabelle translation files are stored.
                """;

    private static final Collection<String> SUPPORTED_VERSIONS_TEXT =
        List.of("Isabelle2023", "Isabelle2024-RC1", "Isabelle2024", "Isabelle2025");

    private static final String infoIsabellePathPanel = String.format(
        """
                Specify the absolute path of the Isabelle folder.
                %s.
                """, createSupportedVersionText());

    private enum IsabelleSupportState {
        SUPPORTED, NOT_SUPPORTED, NO_ISABELLE
    }

    /**
     * Panel for inputting the path to where translations are stored
     */
    private final JTextField translationPathPanel;

    /**
     * Panel for inputting the path to Isabelle installation
     */
    private final JTextField isabellePathPanel;

    /**
     * Input field for timeout in seconds
     */
    private final JSpinner timeoutField;

    /**
     * Supported version info for user
     */
    private final JTextField versionSupported;

    /**
     * The current settings object
     */
    private final IsabelleTranslationSettings settings;

    public IsabelleSettingsProvider() {
        super();
        setHeaderText(getDescription());
        setSubHeaderText(
            "Isabelle settings are stored in: "
                + IsabelleTranslationSettings.SETTINGS_FILE_NEW.getAbsolutePath());
        translationPathPanel = createTranslationPathPanel();
        isabellePathPanel = createIsabellePathPanel();
        timeoutField = createTimeoutField();

        createCheckSupportButton();
        this.versionSupported = createSolverSupported();
        this.settings = IsabelleTranslationSettings.getInstance();


        updateVersionSupportText();
    }

    @Override
    public String getDescription() {
        return "Isabelle Translation";
    }

    @Override
    public JPanel getPanel(MainWindow window) {
        isabellePathPanel
                .setText(settings.getIsabellePath().toString());
        translationPathPanel
                .setText(settings.getTranslationPath().toString());
        timeoutField.setValue(settings.getTimeout());
        return this;
    }

    private JTextField createTranslationPathPanel() {
        return addFileChooserPanel("Location for translation files:", "", infoTranslationPathPanel,
            false, e -> {
            });
    }

    private JTextField createIsabellePathPanel() {
        JTextField isabellePathPanel =
            addFileChooserPanel("Isabelle installation folder:", "", infoIsabellePathPanel,
                false, e -> {
                });
        isabellePathPanel.getDocument().addDocumentListener(new DocumentListener() {

            @Override
            public void insertUpdate(DocumentEvent e) {
                updateVersionSupportText();
            }

            @Override
            public void removeUpdate(DocumentEvent e) {
                updateVersionSupportText();
            }

            @Override
            public void changedUpdate(DocumentEvent e) {
                updateVersionSupportText();
            }
        });
        return isabellePathPanel;
    }

    private JSpinner createTimeoutField() {
        // Use doubles so that the formatter doesn't make every entered String into integers.
        // [see NumberFormatter#stringToValue()].
        JSpinner timeoutSpinner = addNumberField("Timeout:", 1, Integer.MAX_VALUE, 1,
            INFO_TIMEOUT_FIELD,
            e -> settings.setTimeout(e.intValue()));
        // Set the editor so that entered Strings only have three decimal places.
        JSpinner.NumberEditor editor = new JSpinner.NumberEditor(timeoutSpinner, "#");
        // Use floor rounding to be consistent with the value that will be set for the timeout.
        editor.getFormat().setRoundingMode(RoundingMode.FLOOR);
        timeoutSpinner.setEditor(editor);
        return timeoutSpinner;
    }

    protected JButton createCheckSupportButton() {
        JButton checkForSupportButton = new JButton("Check for support");
        checkForSupportButton.setEnabled(true);
        checkForSupportButton
                .addActionListener(arg0 -> updateVersionSupportText());
        addRowWithHelp(null, new JLabel(), checkForSupportButton);
        return checkForSupportButton;
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

    protected JTextField createSolverSupported() {
        JTextField txt = addTextField("Support", getSolverSupportText(),
            createSupportedVersionText(),
            emptyValidator());
        txt.setEditable(false);
        return txt;
    }

    private static String createSupportedVersionText() {
        String supportText = "Supports these Isabelle versions: ";
        supportText = supportText + String.join(", ", SUPPORTED_VERSIONS_TEXT);
        return supportText;
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
    public void applySettings(MainWindow window) throws InvalidSettingsInputException {
        Configuration newConfig = new Configuration();
        newConfig.set(IsabelleTranslationSettings.translationPathKey,
            translationPathPanel.getText());
        newConfig.set(IsabelleTranslationSettings.isabellePathKey, isabellePathPanel.getText());
        settings.readSettings(newConfig);
        updateVersionSupportText();
    }
}

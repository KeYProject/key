/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.isabelletranslation;

import java.math.RoundingMode;
import javax.swing.*;

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
                Timeout for the external solvers in seconds. Fractions of a second are allowed. Example: 6.5
                """;
    private static final String infoTranslationPathPanel =
        """
                Choose where the isabelle translation files are stored.
                """;
    private static final String infoIsabellePathPanel =
        """
                Specify the absolute path of the Isabelle folder.
                """;

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
        this.settings = IsabelleTranslationSettings.getInstance();
    }

    @Override
    public String getDescription() {
        return "Isabelle translation";
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
        return addFileChooserPanel("Store translation to file:", "", infoTranslationPathPanel,
            true, e -> {
            });
    }

    private JTextField createIsabellePathPanel() {
        return addFileChooserPanel("Isabelle folder:", "", infoIsabellePathPanel,
            true, e -> {
            });
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

    @Override
    public void applySettings(MainWindow window) throws InvalidSettingsInputException {
        Configuration newConfig = new Configuration();
        newConfig.set(IsabelleTranslationSettings.translationPathKey,
            translationPathPanel.getText());
        newConfig.set(IsabelleTranslationSettings.isabellePathKey, isabellePathPanel.getText());
        settings.readSettings(newConfig);
    }
}

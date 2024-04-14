package de.uka.ilkd.key.gui.isabelletranslation;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.settings.InvalidSettingsInputException;
import de.uka.ilkd.key.gui.settings.SettingsProvider;
import de.uka.ilkd.key.gui.settings.SettingsPanel;
import de.uka.ilkd.key.settings.Configuration;

import javax.swing.*;

public class IsabelleSettingsProvider extends SettingsPanel implements SettingsProvider {
    private static final String infoTranslationPathPanel =
            """
                    Choose where the isabelle translation files are stored.
                    """;
    private static final String infoIsabellePathPanel =
            """
                    Specify the absolute path of the Isabelle folder.
                    """;

    private final JTextField translationPathPanel;
    private final JTextField isabellePathPanel;

    public IsabelleSettingsProvider() {
        super();
        setHeaderText(getDescription());
        setSubHeaderText(
                "Isabelle settings are stored in: " + IsabelleTranslationSettings.SETTINGS_FILE_NEW.getAbsolutePath());
        translationPathPanel = createTranslationPathPanel();
        isabellePathPanel = createIsabellePathPanel();
    }

    @Override
    public String getDescription() {
        return "Settings for Isabelle translation";
    }

    @Override
    public JPanel getPanel(MainWindow window) {
        isabellePathPanel.setText(IsabelleTranslationSettings.getInstance().getIsabellePath().toString());
        translationPathPanel.setText(IsabelleTranslationSettings.getInstance().getTranslationPath().toString());
        return this;
    }

    protected JTextField createTranslationPathPanel() {
        return addFileChooserPanel("Store translation to file:", "", infoTranslationPathPanel,
                true, e -> {
                });
    }

    protected JTextField createIsabellePathPanel() {
        return addFileChooserPanel("Isabelle folder:", "", infoIsabellePathPanel,
            true, e -> {
            });
    }

    @Override
    public void applySettings(MainWindow window) throws InvalidSettingsInputException {
        Configuration newConfig = new Configuration();
        newConfig.set(IsabelleTranslationSettings.translationPathKey, translationPathPanel.getText());
        newConfig.set(IsabelleTranslationSettings.isabellePathKey, isabellePathPanel.getText());
        IsabelleTranslationSettings.getInstance().readSettings(newConfig);
    }
}

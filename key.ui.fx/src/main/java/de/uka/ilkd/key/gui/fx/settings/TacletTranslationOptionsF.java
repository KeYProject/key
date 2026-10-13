/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.settings;

import javafx.scene.control.Spinner;
import javafx.scene.control.TextField;

import de.uka.ilkd.key.gui.fx.MainWindowF;
import de.uka.ilkd.key.settings.ProofDependentSMTSettings;
import de.uka.ilkd.key.settings.ProofIndependentSMTSettings;

/**
 * The taclet translation options for the SMT solvers, FX port of
 * {@code TacletTranslationOptions} (Swing {@code gui/smt/settings/TacletTranslationOptions.java}):
 * the maximum number of generic sorts per taclet and the optional file the taclet translations
 * are stored to (TacletTranslationOptions.java:44-59); the store option is re-derived from the
 * path on apply and deactivates itself on every restart of KeY (the persisted flag is not read
 * back here, TacletTranslationOptions.java:72).
 */
final class TacletTranslationOptionsF extends SettingsPanelF implements SettingsProviderF {

    private static final String INFO_FILE_CHOOSER_PANEL =
        "Activate this option to store the translations of taclets that are handed over to the "
            + "externals solvers:\n"
            + "1. Choose the folder.\n"
            + "2. Specify the filename:\n"
            + "    %s: the solver's name\n"
            + "    %d: date\n"
            + "    %t: time\n"
            + "    %i: the goal's number\n\n\n"
            + "Example: ./home/translations/Taclet%d_%t_%i_%s.txt\n\n"
            + "Note: After every restart of KeY this option is deactivated.";

    private static final String INFO_MAX_NUMBER_OF_GENERICS =
        "This option specifies how many different generic sorts are allowed within a taclet.\n\n"
            + "Be aware of the fact that too many different generic sorts can overwhelm the "
            + "external solvers. On the other side there are taclets that use a certain amount "
            + "of different generic sorts (see: taclet selection).\n\n"
            + "Rule of thumb: Most of the taclets can be translated by using 2-3 different "
            + "generic sorts.";

    private final TextField fileChooserPanel;
    private final Spinner<Integer> maxNumberOfGenerics;

    TacletTranslationOptionsF() {
        setHeaderText("Taclet Translation Options for SMT");
        fileChooserPanel = addFileChooserPanel("Store taclet translation to file:", "",
            INFO_FILE_CHOOSER_PANEL, true, null);
        maxNumberOfGenerics = addIntNumberField("Maximum number of generic sorts.", 0,
            Integer.MAX_VALUE, 1, 0, INFO_MAX_NUMBER_OF_GENERICS, null);
    }

    @Override
    public String getDescription() {
        return "Taclet Translation";
    }

    @Override
    public javafx.scene.Node getPanel(MainWindowF window) {
        // like the Swing original, the panel works on a copy of the current settings and
        // re-reads them on every dialog open (TacletTranslationOptions.java:67-74)
        ProofDependentSMTSettings pdSettings = SettingsManagerF.getSmtPdSettings(window).clone();
        ProofIndependentSMTSettings piSettings = SettingsManagerF.getSmtPiSettings().clone();
        maxNumberOfGenerics.getValueFactory().setValue(pdSettings.getMaxGenericSorts());
        fileChooserPanel.setText(piSettings.getPathForTacletTranslation());
        return this;
    }

    @Override
    public void apply(MainWindowF window) {
        ProofDependentSMTSettings currentPd = SettingsManagerF.getSmtPdSettings(window);
        ProofIndependentSMTSettings currentPi = SettingsManagerF.getSmtPiSettings();
        currentPd.setMaxGenericSorts(maxNumberOfGenerics.getValue());
        currentPi.setPathForTacletTranslation(fileChooserPanel.getText());
        currentPi
                .setStoreTacletTranslationToFile(!fileChooserPanel.getText().trim().isEmpty());
    }
}

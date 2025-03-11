/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.smt.settings;


import javax.swing.*;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.settings.SettingsManager;
import de.uka.ilkd.key.gui.settings.SettingsPanel;
import de.uka.ilkd.key.gui.settings.SettingsProvider;
import de.uka.ilkd.key.settings.ProofDependentSMTSettings;
import de.uka.ilkd.key.settings.ProofIndependentSMTSettings;

public class TacletTranslationOptions extends SettingsPanel implements SettingsProvider {
    private static final long serialVersionUID = 5273966151509876358L;
    private static final String infoFileChooserPanel =
        """
                Activate this option to store the translations of taclets that are handed over to the externals solvers:
                1. Choose the folder.
                2. Specify the filename:
                \t%s: the solver's name
                \t%d: date
                \t%t: time
                \t%i: the goal's number


                Example: ./home/translations/Taclet%d_%t_%i_%s.txt

                Note: After every restart of KeY this option is deactivated.""";
    private static final String infoMaxNumberOfGenerics =
        """
                This option specifies how many different generic sorts are allowed within a taclet.

                Be aware of the fact that too many different generic sorts can overwhelm the external solvers. On the other side there are taclets that use a certain amount of different generic sorts (see: taclet selection).

                Rule of thumb: Most of the taclets can be translated by using 2-3 different generic sorts.""";
    private final JTextField fileChooserPanel;
    private final JSpinner maxNumberOfGenerics;


    public TacletTranslationOptions() {
        setHeaderText("Taclet Translation Options for SMT");
        fileChooserPanel = createFileChooserPanel();
        maxNumberOfGenerics = createMaxNumberOfGenerics();
    }

    protected JSpinner createMaxNumberOfGenerics() {
        return addNumberField("Maximum number of generic sorts.", 0, Integer.MAX_VALUE, 1,
            infoMaxNumberOfGenerics, emptyValidator());
    }

    protected JTextField createFileChooserPanel() {
        return addFileChooserPanel("Store taclet translation to file:", "", infoFileChooserPanel,
            true, e -> {
            });
    }

    @Override
    public String getDescription() {
        return "Taclet Translation";
    }

    @Override
    public JPanel getPanel(MainWindow window) {
        ProofDependentSMTSettings pdSettings = SettingsManager.getSmtPdSettings(window).clone();
        ProofIndependentSMTSettings piSettings = SettingsManager.getSmtPiSettings().clone();
        maxNumberOfGenerics.setValue(pdSettings.getMaxGenericSorts());
        fileChooserPanel.setText(piSettings.getPathForTacletTranslation());
        // fileChooserPanel.setEnabled(piSettings.storeTacletTranslationToFile);
        return this;
    }

    @Override
    public void applySettings(MainWindow window) {
        ProofDependentSMTSettings currentPd = SettingsManager.getSmtPdSettings(window);
        ProofIndependentSMTSettings currentPi = SettingsManager.getSmtPiSettings();

        currentPd.setMaxGenericSorts((Integer) maxNumberOfGenerics.getValue());
        currentPi.setPathForTacletTranslation(fileChooserPanel.getText());
        currentPi.setStoreTacletTranslationToFile(!fileChooserPanel.getText().trim().isEmpty());
    }
}

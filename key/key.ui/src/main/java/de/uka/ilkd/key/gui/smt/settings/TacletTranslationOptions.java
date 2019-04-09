// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.gui.smt.settings;


import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.settings.SettingsManager;
import de.uka.ilkd.key.gui.settings.SettingsProvider;
import de.uka.ilkd.key.gui.settings.TablePanel;
import de.uka.ilkd.key.settings.ProofDependentSMTSettings;
import de.uka.ilkd.key.settings.ProofIndependentSMTSettings;

import javax.swing.*;

public class TacletTranslationOptions extends TablePanel implements SettingsProvider {
    private static final long serialVersionUID = 1L;
    private static final String infoFileChooserPanel = "Activate this option to store the translations of taclets"
            + " that are handed over to the externals solvers:\n"
            + "1. Choose the folder.\n"
            + "2. Specify the filename:\n"
            + "\t%s: the solver's name\n"
            + "\t%d: date\n"
            + "\t%t: time\n"
            + "\t%i: the goal's number\n"
            + "\n\n"
            + "Example: ./home/translations/Taclet%d_%t_%i_%s.txt"
            + "\n\n"
            + "Note: After every restart of KeY this option"
            + " is deactivated.";
    private static final String infoMaxNumberOfGenerics =
            "This option specifies how many different generic sorts are allowed"
                    + " within a taclet.\n\n"
                    + "Be aware of the fact that too many different generic sorts can"
                    + " overwhelm the external solvers. On the other side there are taclets that"
                    + " use a certain amount of different generic sorts (see: taclet selection).\n\n"
                    + "Rule of thumb: Most of the taclets can be translated by using 2-3 different"
                    + " generic sorts.";
    private final JTextField fileChooserPanel;
    private final JTextField maxNumberOfGenerics;
    private ProofDependentSMTSettings pdSettings;
    private ProofIndependentSMTSettings piSettings;


    public TacletTranslationOptions() {
        fileChooserPanel = createFileChooserPanel();
        maxNumberOfGenerics = createMaxNumberOfGenerics();
    }

    public JTextField createMaxNumberOfGenerics() {
        return addTextField("Maximum number of generic sorts.", "",
                infoMaxNumberOfGenerics, e -> {
                    int value;
                    try {
                        value = Integer.parseInt(maxNumberOfGenerics.getText());
                    } catch (NumberFormatException ex) {
                        value = pdSettings.maxGenericSorts;
                    }
                    pdSettings.maxGenericSorts = value;
                });
    }

    public JTextField createFileChooserPanel() {
        return addFileChooserPanel("Store taclet translation to file:",
                "", infoFileChooserPanel, true, e -> {
                    piSettings.pathForTacletTranslation = fileChooserPanel.getText();
                    //TODO piSettings.storeTacletTranslationToFile = fileChooserPanel.isSelected();
                });
    }

    @Override
    public String getDescription() {
        return "Taclet Translation";
    }

    @Override
    public JComponent getPanel(MainWindow window) {
        pdSettings = SettingsManager.getSmtPdSettings(window);
        piSettings = SettingsManager.getSmtPiSettings();
        maxNumberOfGenerics.setText(Integer.toString(pdSettings.maxGenericSorts));
        fileChooserPanel.setText(piSettings.pathForTacletTranslation);
        fileChooserPanel.setEnabled(piSettings.storeTacletTranslationToFile);
        return this;
    }

    @Override
    public void applySettings(MainWindow window) {
    }
}


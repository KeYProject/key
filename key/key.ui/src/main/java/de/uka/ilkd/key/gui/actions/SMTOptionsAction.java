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

package de.uka.ilkd.key.gui.actions;

import de.uka.ilkd.key.gui.fonticons.IconFactory;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.settings.SettingsManager;

import java.awt.event.ActionEvent;


/**
 * creates a menu allowing to choose the external prover to be used
 */
public class SMTOptionsAction extends MainWindowAction {
    private static final long serialVersionUID = 1L;

    public SMTOptionsAction(MainWindow mainWindow) {
        super(mainWindow);
        setName("Show SMT Solver Options");
        setIcon(IconFactory.toolbox(16));
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        SettingsManager.getInstance().showSettingsDialog(mainWindow, SettingsManager.SMT_SETTINGS);

        /*
        ProofDependentSMTSettings pdSettings = ProofSettings.DEFAULT_SETTINGS.getSMTSettings();
        Proof proof = this.getMediator().getSelectedProof();
        if (proof != null) {
            pdSettings = proof.getSettings().getSMTSettings();
        }
        ProofIndependentSMTSettings piSettings = ProofIndependentSettings.DEFAULT_INSTANCE.getSMTSettings();

        TestGenerationSettings tgSettings = ProofIndependentSettings.DEFAULT_INSTANCE.getTestGenerationSettings();
        final SMTSettingsModel settingsModel = new SMTSettingsModel(new SMTSettings(pdSettings, piSettings, proof), tgSettings);
        bottomComponent = new JLabel("No proof has been loaded: those are the default settings.");
        */

    }
}

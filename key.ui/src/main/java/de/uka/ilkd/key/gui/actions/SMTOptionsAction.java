/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.fonticons.IconFactory;
import de.uka.ilkd.key.gui.settings.SettingsManager;


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
         * ProofDependentSMTSettings pdSettings = ProofSettings.DEFAULT_SETTINGS.getSMTSettings();
         * Proof proof = this.getMediator().getSelectedProof(); if (proof != null) { pdSettings =
         * proof.getSettings().getSMTSettings(); } ProofIndependentSMTSettings piSettings =
         * ProofIndependentSettings.DEFAULT_INSTANCE.getSMTSettings();
         *
         * TestGenerationSettings tgSettings =
         * ProofIndependentSettings.DEFAULT_INSTANCE.getTestGenerationSettings(); final
         * SMTSettingsModel settingsModel = new SMTSettingsModel(new SMTSettings(pdSettings,
         * piSettings, proof), tgSettings); bottomComponent = new
         * JLabel("No proof has been loaded: those are the default settings.");
         */

    }
}

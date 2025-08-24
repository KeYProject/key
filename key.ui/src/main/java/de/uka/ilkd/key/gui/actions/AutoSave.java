/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.settings.ProofIndependentSettings;

import org.key_project.util.java.IOUtil;

public class AutoSave extends MainWindowAction {
    public static final int DEFAULT_PERIOD = 2000;

    public AutoSave(MainWindow mainWindow) {
        super(mainWindow);
        setTooltip("Proofs will be automatically saved to +" + IOUtil.getTempDirectory()
            + "periodically and when finished.");
        setName("Auto Save Proofs");
        setSelected(
            ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings().autoSavePeriod() > 0);

        enabledOnAnActiveProof();
        enabledWhenNotInAutoMode();
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        int p = isSelected() ? DEFAULT_PERIOD : 0;
        ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings().setAutoSave(p);
        this.getMediator().setAutoSave(p);
    }

}

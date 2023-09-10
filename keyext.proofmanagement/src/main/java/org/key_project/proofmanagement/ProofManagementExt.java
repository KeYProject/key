/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.proofmanagement;

import java.awt.event.*;
import java.util.List;
import javax.annotation.Nonnull;
import javax.swing.*;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.KeyAction;
import de.uka.ilkd.key.gui.extension.api.KeYGuiExtension;

/**
 * @author Wolfram Pfeifer
 * @version 1 (16/09/2021)
 */
@KeYGuiExtension.Info(name = "Proof management",
    optional = true,
    description = "Allows to run soundness checks on proof bundles.",
    experimental = false)
public class ProofManagementExt implements
        KeYGuiExtension, KeYGuiExtension.MainMenu {

    private static final String MENU_PM = "Proof Management";

    @Nonnull
    @Override
    public List<Action> getMainMenuActions(@Nonnull MainWindow mainWindow) {

        return List.of(new CheckAction());
    }

    private static class CheckAction extends KeyAction {
        private CheckAction() {
            putValue(NAME, "Check proof bundle ...");
            // putValue(SMALL_ICON, IconFactory.INTERLOG_TRY_APPLY.get());
            setMenuPath(MENU_PM);
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            JDialog checkConfigDialog = new CheckConfigDialog(MainWindow.getInstance(),
                "Check configuration", true);
            checkConfigDialog.setVisible(true);
            checkConfigDialog.dispose();
        }
    }

    // TODO: not yet implemented
    /*
     * private static class MergeAction extends KeyAction {
     * private MergeAction() {
     * putValue(NAME, "Merge proof bundles ...");
     * //putValue(SMALL_ICON, IconFactory.INTERLOG_TRY_APPLY.get());
     * setMenuPath(MENU_PM);
     * }
     *
     * @Override
     * public void actionPerformed(ActionEvent e) {
     *
     * }
     * }
     */

    // TODO: not yet implemented
    /*
     * private static class BundleAction extends KeyAction {
     * private BundleAction() {
     * putValue(NAME, "Create proof bundle from directory ...");
     * //putValue(SMALL_ICON, IconFactory.INTERLOG_TRY_APPLY.get());
     * setMenuPath(MENU_PM);
     * }
     *
     * @Override
     * public void actionPerformed(ActionEvent e) {
     *
     * }
     * }
     */

    public static void main(String[] args) {
        JDialog checkConfigDialog = new CheckConfigDialog(null, "Check configuration", true);
        checkConfigDialog.setVisible(true);
        checkConfigDialog.dispose();
    }
}

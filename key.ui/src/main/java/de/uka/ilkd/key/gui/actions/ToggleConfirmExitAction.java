/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;
import javax.swing.JCheckBoxMenuItem;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.settings.ProofIndependentSettings;

import org.jspecify.annotations.NullMarked;

@NullMarked
public class ToggleConfirmExitAction extends MainWindowAction {

    /**
     *
     */
    private static final long serialVersionUID = 3453843972242689758L;

    /**
     * The action-configuration setters are called on {@code this} while the receiver is still
     * under initialization (EISOP initialization check); safe here, suppressed with a scoped key.
     */
    @SuppressWarnings("nullness:method.invocation.invalid")
    public ToggleConfirmExitAction(MainWindow mainWindow) {
        super(mainWindow);
        setTooltip("Ask for extra confirmation when trying to exit the prover");
        setName("Confirm Exit");
        setSelected(ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().confirmExit());
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        boolean b = ((JCheckBoxMenuItem) e.getSource()).isSelected();
        ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().setConfirmExit(b);
    }

}

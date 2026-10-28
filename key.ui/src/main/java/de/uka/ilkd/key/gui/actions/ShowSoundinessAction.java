/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.soundiness.SoundinessDialog;
import de.uka.ilkd.key.proof.Proof;

import org.jspecify.annotations.NullMarked;

/**
 * Action to show the soundiness report for the currently selected proof.
 *
 * @author opencode
 * @since 3.0
 */
@NullMarked
public class ShowSoundinessAction extends MainWindowAction {

    private static final long serialVersionUID = 1L;

    /**
     * The action-configuration calls and the {@code enableWhenProofLoaded(this)} registration
     * operate on {@code this} while the receiver is still under initialization (EISOP
     * initialization check); safe here since the listener only reacts to later selection events,
     * suppressed with scoped keys.
     */
    @SuppressWarnings({ "nullness:method.invocation.invalid",
        "nullness:argument.type.incompatible" })
    public ShowSoundinessAction(MainWindow mainWindow) {
        super(mainWindow);
        setName("Show Soundiness Report");
        // TODO Can we have an extension w/o extra menu?
        putValue(KeyAction.PATH, "Show Soundiness Report");
        getMediator().enableWhenProofLoaded(this);
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        Proof proof = getMediator().getSelectedProof();
        if (proof != null) {
            SoundinessDialog dialog = new SoundinessDialog(mainWindow, proof);
            dialog.setVisible(true);
        }
    }
}

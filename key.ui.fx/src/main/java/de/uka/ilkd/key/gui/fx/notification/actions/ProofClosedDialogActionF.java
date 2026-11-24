/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.notification.actions;

import de.uka.ilkd.key.gui.fx.notification.NotificationActionF;
import de.uka.ilkd.key.gui.fx.notification.NotificationManagerF;
import de.uka.ilkd.key.gui.fx.notification.ProofClosedDialogF;
import de.uka.ilkd.key.gui.fx.notification.events.NotificationEventF;
import de.uka.ilkd.key.gui.fx.notification.events.ProofClosedNotificationEventF;
import de.uka.ilkd.key.proof.Proof;

/**
 * Opens the {@link ProofClosedDialogF} (statistics summary) for a closed proof.
 * <p>
 * Port of the Swing original {@code key.ui/src/main/java/de/uka/ilkd/key/gui/notification/
 * actions/ProofClosedJTextPaneDisplay.java}, which opens the {@code ShowProofStatistics.Window}
 * for the closed proof. The "no proof" fallback (a Swing {@code JOptionPane} with "Proof Closed.
 * No statistics available.", ProofClosedJTextPaneDisplay.java:70-78) maps to a toast, consistent
 * with the FX toast-instead-of-modal-dialog deviation.
 */
public final class ProofClosedDialogActionF implements NotificationActionF {

    @Override
    public boolean execute(NotificationEventF event) {
        if (event instanceof ProofClosedNotificationEventF pcne) {
            Proof proof = pcne.getProof();
            if (proof != null) {
                ProofClosedDialogF.show(proof);
            } else {
                NotificationManagerF.getInstance()
                        .notify("Proof Closed. No statistics available.",
                            NotificationManagerF.Kind.INFO);
            }
        }
        return true;
    }
}

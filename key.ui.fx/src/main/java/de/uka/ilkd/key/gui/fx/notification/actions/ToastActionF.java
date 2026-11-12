/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.notification.actions;

import de.uka.ilkd.key.gui.fx.notification.NotificationActionF;
import de.uka.ilkd.key.gui.fx.notification.NotificationManagerF;
import de.uka.ilkd.key.gui.fx.notification.events.AbandonTaskEventF;
import de.uka.ilkd.key.gui.fx.notification.events.ExceptionFailureEventF;
import de.uka.ilkd.key.gui.fx.notification.events.ExitKeYEventF;
import de.uka.ilkd.key.gui.fx.notification.events.GeneralFailureEventF;
import de.uka.ilkd.key.gui.fx.notification.events.GeneralInformationEventF;
import de.uka.ilkd.key.gui.fx.notification.events.NotificationEventF;
import de.uka.ilkd.key.gui.fx.notification.events.ProofClosedNotificationEventF;
import de.uka.ilkd.key.proof.Proof;

/**
 * Displays a notification event as a toast via the {@link NotificationManagerF}.
 * <p>
 * This is the FX counterpart of the Swing {@code JTextPane}/display actions of the
 * {@code key.ui} notification package ({@code GeneralInformationJTextPaneDisplay},
 * {@code GeneralFailureJTextPaneDisplay}, {@code ExceptionFailureNotificationDialog},
 * {@code ShowDisplayPane}): the Swing originals show modal {@code JOptionPane} message dialogs,
 * which the FX UI deliberately replaces by toasts (documented deviation, same as the Swing
 * {@code popupWarning} mapping in {@code MainWindowF}).
 */
public final class ToastActionF implements NotificationActionF {

    @Override
    public boolean execute(NotificationEventF event) {
        NotificationManagerF manager = NotificationManagerF.getInstance();
        // ExceptionFailureEventF extends GeneralFailureEventF, so check it first
        if (event instanceof ExceptionFailureEventF ex) {
            manager.notify(ex.getErrorMessage(), NotificationManagerF.Kind.ERROR);
        } else if (event instanceof GeneralFailureEventF failure) {
            manager.notify(failure.getErrorMessage(), NotificationManagerF.Kind.ERROR);
        } else if (event instanceof GeneralInformationEventF info) {
            // Swing uses the event context (e.g. "Automated proof search") as dialog title
            manager.notify(info.getContext() + ": " + info.getMessage(),
                NotificationManagerF.Kind.INFO);
        } else if (event instanceof ProofClosedNotificationEventF closed) {
            Proof proof = closed.getProof();
            manager.notify("Proof closed: " + (proof == null ? "" : proof.name()),
                NotificationManagerF.Kind.INFO);
        } else if (event instanceof AbandonTaskEventF) {
            manager.notify("Proof task abandoned.", NotificationManagerF.Kind.WARNING);
        } else if (event instanceof ExitKeYEventF) {
            manager.notify("KeY is shutting down.", NotificationManagerF.Kind.INFO);
        } else {
            manager.notify("Notification: " + event, NotificationManagerF.Kind.INFO);
        }
        return true;
    }
}

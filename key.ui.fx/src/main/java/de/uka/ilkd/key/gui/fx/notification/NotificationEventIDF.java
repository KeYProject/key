/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.notification;

/**
 * Identifiers for the kinds of events handled by the notification framework.
 * <p>
 * Port of the Swing original {@code key.ui/src/main/java/de/uka/ilkd/key/gui/notification/
 * NotificationEventID.java}. The Swing enum lives in the {@code key.ui} module, which is no
 * dependency of {@code key.ui.fx}, hence this FX-side copy (name parity deviation: {@code F}
 * suffix, as for all ported FX classes).
 */
public enum NotificationEventIDF {

    /** tasks notifying about proof closed events have this ID */
    PROOF_CLOSED,
    /** tasks notifying about abandoned tasks have this ID */
    TASK_ABANDONED,
    /** tasks notifying about general failures */
    GENERAL_FAILURE,
    /** tasks notifying the user when KeY is shutdown have this ID */
    EXIT_KEY,
    /** tasks used to inform the user should have this ID */
    GENERAL_INFORMATION,
    /** tasks used to inform the user about exceptions causing a failure have this ID */
    EXCEPTION_CAUSED_FAILURE
}

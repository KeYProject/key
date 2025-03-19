/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.notification;

/**
 * This interface constants used to uniquely identify KeY system events
 *
 * Refactored this type into an enum. // Kai Walisch 06/2015
 *
 * @author bubel
 */
public enum NotificationEventID {

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
    /** tasks used to inform the user should have this ID */
    EXCEPTION_CAUSED_FAILURE

}

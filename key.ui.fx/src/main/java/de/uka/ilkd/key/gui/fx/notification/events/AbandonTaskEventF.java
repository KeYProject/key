/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.notification.events;

import de.uka.ilkd.key.gui.fx.notification.NotificationEventIDF;

/**
 * Emitted after removing a proof task.
 * <p>
 * Port of the Swing original {@code key.ui/src/main/java/de/uka/ilkd/key/gui/notification/
 * events/AbandonTaskEvent.java}. Note: the abandon-task action is not ported yet (parity audit
 * {@code parity-mainwindow.md} gap 12), so no app-level trigger fires this event today; the
 * class completes the framework for future wiring.
 */
public class AbandonTaskEventF extends NotificationEventF {

    /**
     * creates an event
     */
    public AbandonTaskEventF() {
        super(NotificationEventIDF.TASK_ABANDONED);
    }
}

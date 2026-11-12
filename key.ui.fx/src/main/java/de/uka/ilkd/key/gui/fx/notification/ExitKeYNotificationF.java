/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.notification;

/**
 * This task takes care for a notification when exiting KeY.
 * <p>
 * Port of the Swing original {@code key.ui/src/main/java/de/uka/ilkd/key/gui/notification/
 * ExitKeYNotification.java}. Swing overrides {@code execute} to marshal with
 * {@code SwingUtilities.invokeAndWait} (ExitKeYNotification.java:43-56) because the exit flow
 * continues after the notification; in JavaFX {@link NotificationTaskF#execute} already runs
 * synchronously when called on the FX application thread (where the FX exit flow lives), so no
 * override is needed. Declares no actions, like Swing. Note: the FX exit flow itself is not
 * ported yet (parity audit {@code parity-mainwindow.md} gap 5), so no trigger fires this event
 * today.
 */
public class ExitKeYNotificationF extends NotificationTaskF {

    @Override
    public NotificationEventIDF getEventID() {
        return NotificationEventIDF.EXIT_KEY;
    }
}

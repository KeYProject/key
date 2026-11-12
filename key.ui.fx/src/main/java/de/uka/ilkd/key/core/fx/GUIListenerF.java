/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.core.fx;

import java.util.EventListener;
import java.util.EventObject;

/**
 * Defines the interface for an object that listens to actions of gui components, e.g. it is
 * informed if a gui component requests modal access — the JavaFX counterpart of
 * {@code de.uka.ilkd.key.gui.GUIListener} in the Swing module {@code key.ui} (GUIListener.java
 * :14-27), which is not importable into {@code key.ui.fx} (no dependency on key.ui).
 * <p>
 * Listeners are registered at the mediator ({@link KeYMediatorF#addGUIListener(GUIListenerF)}),
 * which fires the three events via {@link KeYMediatorF#fireModalDialogOpened(EventObject)},
 * {@link KeYMediatorF#fireModalDialogClosed(EventObject)} and
 * {@link KeYMediatorF#fireShutDown(EventObject)} — the exit flow of {@code MainWindowF} fires
 * the shutdown event like Swing's {@code ExitMainAction.exitMainWithoutInteraction}
 * (ExitMainAction.java:83).
 */
public interface GUIListenerF extends EventListener {

    /** invoked if a frame that wants modal access is opened */
    void modalDialogOpened(EventObject e);

    /** invoked if the frame holding modal access has been closed */
    void modalDialogClosed(EventObject e);

    /** invoked if the user wants to abort the proving session */
    void shutDown(EventObject e);
}

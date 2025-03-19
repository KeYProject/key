/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui;

import java.util.EventListener;
import java.util.EventObject;

/**
 * GUIListener defines the interface for an object that listens to actions of gui components, e.g.
 * it is informed if a gui component requests modal access.
 */
public interface GUIListener extends EventListener {

    /** invoked if a frame that wants modal access is opened */
    void modalDialogOpened(EventObject e);

    /** invoked if the frame holding modal access has been closed */
    void modalDialogClosed(EventObject e);

    /** invoked if the user wants to abort the proving session */
    void shutDown(EventObject e);

}

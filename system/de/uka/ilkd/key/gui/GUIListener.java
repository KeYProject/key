// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.gui;
import java.util.EventListener;

/** 
 * GUIListener defines the interface for an object that listens to
 * actions of gui components, e.g. it is informed if a gui component
 * requests modal access. 
 */
public interface GUIListener extends EventListener {

    /** invoked if a frame that wants modal access is opened */
    void modalDialogOpened(GUIEvent e);

    /** invoked if the frame holding modal access has been closed */
    void modalDialogClosed(GUIEvent e);

    /** invoked if the user wants to abort the proving session */
    void shutDown(GUIEvent e);

} 

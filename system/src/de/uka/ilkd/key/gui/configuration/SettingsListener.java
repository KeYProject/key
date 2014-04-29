// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.gui.configuration;

import de.uka.ilkd.key.gui.GUIEvent;


/** This interface is implemented by objects that listen to settings
 * object. An object implementing the settins interface will call the
 * method settingChanged of the listener
 */
public interface SettingsListener {
    
    /** called by the Settings object to inform the listener that its
     * state has changed
     * @param e the Event sent to the listener
     */
    void settingsChanged(GUIEvent e);
}
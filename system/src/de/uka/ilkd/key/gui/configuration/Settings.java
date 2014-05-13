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

import java.util.Properties;

/** This interface is implemented by classes that are used to store
 * settings for different proposes (like active heuristics, which LDTs
 * to use etc.) 
 */
public interface Settings {
    
    /** gets a Properties object and has to perform the necessary
     * steps in order to change this object in a way that it
     * represents the stored settings
     * <code>sender</code> is the object calling this method.
     */
    void readSettings(Object sender, Properties props);

    /** The settings to store are written to the given Properties object.
     * @param props the Properties object where to write the settings as (key, value) pair
     * <code>sender</code> is the object calling this method.
     */
    void writeSettings(Object sender, Properties props);

    /** adds a listener to the settings object 
     * @param l the listener
     */
    void addSettingsListener(SettingsListener l);
}
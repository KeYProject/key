// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.gui.configuration;

/** The ConfigChangeListener is notified if the UI settings in 
 * class Config change.
 */
public interface ConfigChangeListener {

    /** focused node has changed */
    void configChanged(ConfigChangeEvent e);

} 

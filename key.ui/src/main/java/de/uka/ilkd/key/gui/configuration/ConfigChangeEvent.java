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

/** An event that indicates that the users focused node or proof has
 * changed */ 

public class ConfigChangeEvent {
    
    /** the source of this event */
    private Config source;

    /** creates a new ConfigChangeEvent
     * @param source the Config where the event had its
     * origin
     */
    public ConfigChangeEvent(Config source) {
	this.source = source;
    }

    /** returns the Config that caused this event
     * @return the Config that caused this event
     */
    public Config getSource() {
	return source;
    }

}
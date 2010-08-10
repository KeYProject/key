// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.gui;

/** An event that indicates that the users focused node or proof has
 * changed */ 

public class KeYSelectionEvent {
    
    /** the source of this event */
    private KeYSelectionModel source;

    /** creates a new SelectedNodeEvent
     * @param source the SelectedNodeModel where the event had its
     * origin
     */
    public KeYSelectionEvent(KeYSelectionModel source) {
	this.source = source;
    }

    /** returns the KeYSelectionModel that caused this event
     * @return the KeYSelectionModel that caused this event
     */
    public KeYSelectionModel getSource() {
	return source;
    }

}

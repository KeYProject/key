// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof;

import java.util.EventObject;

public class ConstraintTableEvent extends EventObject {
    
    /** creates a new gui event 
     * @param source Object that is the source of the event
     */
    public ConstraintTableEvent(Object source) {
	super(source);
    }

    /** the source that caused the event 
     * @return the source that caused the event 
     */
    public Object getSource() {
	return super.getSource();
    }

}

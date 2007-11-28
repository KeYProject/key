// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2004 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.gui.assistant;

/**
 * The input for the proof assistant AI has to implement this interface
 */
public interface AIInput {
    
    /** a button on the toolbar has been pressed */
    int TOOLBAR_EVENT = 0;

    /** an item on the menu bar has been selected */
    int MENUBAR_EVENT = 1;

    /** some rule application has been used/created/selected */
    int RULE_APPLICATION_EVENT = 2;


    /**
     * return the classification ID of this input
     */
    int getInputID();

}

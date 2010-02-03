// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
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
 * This is one of the simplest actions, display just a text on the
 * user interface of the proof assistant.
 */
public class DisplayTextAction implements AIAction {
    
    private final String text;

    /**
     * display the given text 
     */
    public DisplayTextAction(String text) {
	this.text = text;
    }
			     			     
    /**
     * execute the action
     */
    public void execute(ProofAssistantController ctrl) {
	ctrl.displayText(text);
    }

}

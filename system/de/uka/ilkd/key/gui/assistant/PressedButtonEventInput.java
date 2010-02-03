// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.gui.assistant;

import javax.swing.AbstractButton;

/**
 * This is a rather concrete input class and needs to be generalized
 * some times.
 */
public class PressedButtonEventInput implements AIInput {
    
    private final AbstractButton pressedButton;
    private final int inputID;

    public PressedButtonEventInput(AbstractButton pressed, int id) {
	this.pressedButton = pressed;
	this.inputID = id;
    }

    public AbstractButton getPressedButton() {
	return pressedButton;
    }

    /**
     * return the classification ID of this input
     */
    public int getInputID() {
	return inputID;
    }

}

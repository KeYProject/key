// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.java;

import de.uka.ilkd.key.java.declaration.ArrayOfModifier;

/**
 *  Declaration.
 * taken from COMPOST and changed to achieve an immutable structure
 */
public interface Declaration extends NonTerminalProgramElement {

    /**
     * Get the modifiers.
     * @return the (original) list of modifiers wrapped .
     */
    ArrayOfModifier getModifiers();
}

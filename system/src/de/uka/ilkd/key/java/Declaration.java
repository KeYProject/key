// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 


package de.uka.ilkd.key.java;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.java.declaration.Modifier;


/**
 *  Declaration.
 * taken from COMPOST and changed to achieve an immutable structure
 */
public interface Declaration extends NonTerminalProgramElement {

    /**
     * Get the modifiers.
     * @return the (original) list of modifiers wrapped .
     */
    ImmutableArray<Modifier> getModifiers();
}

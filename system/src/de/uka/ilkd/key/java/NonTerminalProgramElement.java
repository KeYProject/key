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

package de.uka.ilkd.key.java;

/**
 *  Non terminal program element.
 * taken from COMPOST and changed to achieve an immutable structure
 */

public interface NonTerminalProgramElement extends ProgramElement {

 /**
 *      Returns the number of children of this node.
 *      @return an int giving the number of children of this node
 */
    int getChildCount();

 /**
 *      Returns the child at the specified index in this node's "virtual"
 *      child array.
 *      @param index an index into this node's "virtual" child array
 *      @return the program element at the given position
 *      @exception ArrayIndexOutOfBoundsException if <tt>index</tt> is out
 *                 of bounds
 */
    ProgramElement getChildAt(int index);
    
}
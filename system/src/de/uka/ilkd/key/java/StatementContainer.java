// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//


package de.uka.ilkd.key.java;


/**
 *  Statement container.
 * taken from COMPOST and changed to achieve an immutable structure
 */

public interface StatementContainer extends NonTerminalProgramElement {

    /**
 *      Get the number of statements in this container.
 *      @return the number of statements.
     */
    int getStatementCount();

    /*
      Return the statement at the specified index in this node's
      "virtual" statement array.
      @param index an index for a statement.
      @return the statement with the given index.
      @exception ArrayIndexOutOfBoundsException if <tt>index</tt> is out
      of bounds.
    */
    Statement getStatementAt(int index);
}

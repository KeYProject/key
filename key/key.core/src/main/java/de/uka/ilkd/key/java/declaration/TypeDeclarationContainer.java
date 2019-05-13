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

package de.uka.ilkd.key.java.declaration;

import de.uka.ilkd.key.java.NonTerminalProgramElement;

/**
 *  Type declaration container.
 * taken from COMPOST and changed to achieve an immutable structure
 */

public interface TypeDeclarationContainer extends NonTerminalProgramElement {

    /**
 *      Get the number of type declarations in this container.
 *      @return the number of type declarations.
     */
    int getTypeDeclarationCount();

    /*
      Return the type declaration at the specified index in this node's
      "virtual" type declaration array.
      @param index an index for a type declaration.
      @return the type declaration with the given index.
      @exception ArrayIndexOutOfBoundsException if <tt>index</tt> is out
      of bounds.
    */
    TypeDeclaration getTypeDeclarationAt(int index);
}
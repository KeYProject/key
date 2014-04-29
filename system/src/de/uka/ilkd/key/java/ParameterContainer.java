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

import de.uka.ilkd.key.java.declaration.ParameterDeclaration;

/**
 *    Describes program elements that contain
 *    {@link recoder.java.declaration.ParameterDeclaration}s.
 * taken from RECODER and changed to achieve an immutable structure
 */

public interface ParameterContainer extends StatementContainer {

    /**
 *      Get the number of parameters in this container.
 *      @return the number of parameters.
     */
    int getParameterDeclarationCount();

    /*
      Return the parameter declaration at the specified index in this node's
      "virtual" parameter declaration array.
      @param index an index for a parameter declaration.
      @return the parameter declaration with the given index.
      @exception ArrayIndexOutOfBoundsException if <tt>index</tt> is out
      of bounds.
    */
    ParameterDeclaration getParameterDeclarationAt(int index);
}
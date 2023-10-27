/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java;

import de.uka.ilkd.key.java.declaration.ParameterDeclaration;

/**
 * Describes program elements that contain {@link recoder.java.declaration.ParameterDeclaration}s.
 * taken from RECODER and changed to achieve an immutable structure
 */

public interface ParameterContainer extends StatementContainer {

    /**
     * Get the number of parameters in this container.
     *
     * @return the number of parameters.
     */
    int getParameterDeclarationCount();

    /**
     * Return the parameter declaration at the specified index in this node's "virtual" parameter
     * declaration array.
     *
     * @param index an index for a parameter declaration.
     * @return the parameter declaration with the given index.
     * @exception ArrayIndexOutOfBoundsException if <tt>index</tt> is out of bounds.
     */
    ParameterDeclaration getParameterDeclarationAt(int index);
}

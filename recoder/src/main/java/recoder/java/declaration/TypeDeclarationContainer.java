/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.declaration;

import recoder.java.NonTerminalProgramElement;

/**
 * Type declaration container.
 *
 * @author <TT>AutoDoc</TT>
 */

public interface TypeDeclarationContainer extends NonTerminalProgramElement {

    /**
     * Get the number of type declarations in this container.
     *
     * @return the number of type declarations.
     */
    int getTypeDeclarationCount();

    /*
     * Return the type declaration at the specified index in this node's "virtual" type declaration
     * array. @param index an index for a type declaration. @return the type declaration with the
     * given index.
     *
     * @exception ArrayIndexOutOfBoundsException if <tt> index </tt> is out of bounds.
     */
    TypeDeclaration getTypeDeclarationAt(int index);
}

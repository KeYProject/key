/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.reference;

import recoder.java.NonTerminalProgramElement;

/**
 * Type reference container.
 *
 * @author <TT>AutoDoc</TT>
 */

public interface TypeReferenceContainer extends NonTerminalProgramElement {

    /**
     * Get the number of type references in this container.
     *
     * @return the number of type references.
     */
    int getTypeReferenceCount();

    /*
     * Return the type reference at the specified index in this node's "virtual" type reference
     * array. @param index an index for a type reference. @return the type reference with the given
     * index. @exception ArrayIndexOutOfBoundsException if <tt> index </tt> is out of bounds.
     */
    TypeReference getTypeReferenceAt(int index);
}

/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
// Modified by KeY

package de.uka.ilkd.key.java.abstraction;

import de.uka.ilkd.key.java.reference.TypeReference;

/**
 * A program model element representing array types.
 */
public interface ArrayType extends Type {

    /**
     * returns the type reference to the arrays base type
     *
     * @return the type reference to the arrays base type
     */
    TypeReference getBaseType();

    /**
     * returns the dimension of the array
     *
     * @return an int containing the array's dimension
     */
    int getDimension();

    /**
     * name of the array type
     */
    String getName();

    /**
     * full name of the array type
     */
    String getFullName();

    /**
     * full name of the array in alternative form, i.e. e.g. <code>int[]</code> instead of
     * <code>[I</code>
     */
    String getAlternativeNameRepresentation();
}

// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.util;


/**
 * Utility class which provides methods for Array-handling.
 */
public class Array {

    public static Object[] reverse(Object[] array) {
        if (array == null) {
            return null;
        }

        int l = array.length;
        Object[] result = new Object[l];

        for (int i = 0; i < l; i++) {
            result[i] = array[l - 1 - i];
        }

        return result;
    }

}

// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.asmkey.util;

import java.lang.reflect.Array;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;


/** Static methods to print and copy arrays.
 * 
 * @see CollectionUtil
 * @author Hubert Schmid
 */

public final class ArrayUtil {

    private ArrayUtil() {}

    /** Returns a string representing all elements in the array. The
     * elements are separated with <tt>infix</tt>. */
    public static String toString(Object[] array, String infix) {
        if (array == null) {
            return "null";
        } else if (array.length == 0) {
            return "[]";
        } else {
            StringBuffer sb = new StringBuffer('[').append(array[0]);
            for (int i = 1; i < array.length; ++i) {
                sb.append(infix).append(array[i]);
            }
            sb.append(']');
            return sb.toString();
        }
    }

    /** return @{link #toString(Object[], String) toString(array,
     * ",")} */
    public static String toString(Object[] array) {
        return toString(array, CollectionUtil.DEFAULT_INFIX);
    }

    /** Returns an unmodifiable list containing the elements of the
     * array. */
    public static List toList(Object[] array) {
        if (array == null) {
            return null;
        } else {
            return Collections.unmodifiableList(Arrays.asList(array));
        }
    }

    /** Returns a <i>shallow</i> copy of the array. */
    public static Object[] copy(Object[] array) {
        if (array == null) {
            return new Object[0];
        } else {
            Object[] a = (Object[]) Array.newInstance(array.getClass().getComponentType(), array.length);
            System.arraycopy(array, 0, a, 0, array.length);
            return a;
        }
    }

}

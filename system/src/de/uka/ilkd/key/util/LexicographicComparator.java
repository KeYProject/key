// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.util;

import java.util.Comparator;

/**
 * Compares arrays of comparable objects (e.g., Integer).
 * Returns negative numbers if o1 is less than o2,
 * positive numbers if o2 is less than o1,
 * and 0 if they are equal.
 * If the arrays are equal up to the length of the shorter one,
 * the shorter one is considered less.
 * @author bruns
 */
public final class LexicographicComparator<U> 
implements Comparator<Comparable<U>[]> {

    @Override
    public int compare(Comparable<U>[] o1, Comparable<U>[] o2) {
        if (o1 == null && o2 == null) return 0;
        if (o1 == null) return Integer.MIN_VALUE+1;
        if (o2 == null) return Integer.MAX_VALUE;
        for (int i= 0; i < o1.length && i < o2.length; i++) {
            @SuppressWarnings("unchecked")
            int c = o2[i].compareTo((U) o1[i]);
            if (c != 0) return c;
        }
        if (o1.length < o2.length) return 1;
        if (o1.length > o2.length) return -1;
        return 0;
    }
}
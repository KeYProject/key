// @(#)$Id: JMLInfiniteIntegerClass.java 1.1 Mon, 02 May 2005 14:31:03 +0200 engelc $

// Copyright (C) 1998, 1999 Iowa State University

// This file is part of JML

// JML is free software; you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation; either version 2, or (at your option)
// any later version.

// JML is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with JML; see the file COPYING.  If not, write to
// the Free Software Foundation, 675 Mass Ave, Cambridge, MA 02139, USA.

package org.jmlspecs.models;

import java.math.BigInteger;

/** Class with common code to implement JMLInfiniteInteger.
 *
 * @version $Revision: 1.1 $
 * @author Gary T. Leavens
 * @see java.math.BigInteger
 */
//-@ immutable
public abstract /*@ pure @*/ class JMLInfiniteIntegerClass
    implements JMLInfiniteInteger {

    //@ public invariant owner == null;

    /** Return a clone of this integer.
     */
    public Object clone() { return this; }

    /** Tell whether this integer is equal to the argument.
     ** Note that comparisons to BigIntegers are also handled.
     */
    public boolean equals(Object o) {
        if (o != null) {
            try {
                return compareTo(o) == 0;
            } catch (ClassCastException cce) {
                return false;
            }
        } else {
            return false;
        }
    }

    /** Compare this to n, returning a comparison code.
     *  @param n the object this is compared to.
     */
    public abstract int compareTo(/*@ non_null @*/ JMLInfiniteInteger n);

    /** Tell if this integer is greater than or equal to the argument.
     */
    public boolean greaterThanOrEqualTo(JMLInfiniteInteger n) {
        return compareTo(n) >= 0;
    }

    /** Tell if this integer is less than or equal to the argument.
     */
    public boolean lessThanOrEqualTo(JMLInfiniteInteger n) {
        return compareTo(n) <= 0;
    }

    /** Tell if this integer is strictly greater than the argument.
     */
    public boolean greaterThan(JMLInfiniteInteger n) {
        return compareTo(n) > 0;
    }

    /** Tell if this integer is strictly less than the argument.
     */
    public boolean lessThan(JMLInfiniteInteger n) {
        return compareTo(n) < 0;
    }

    /** Return the absolute value of this integer.
     */
    public JMLInfiniteInteger abs() {
        if ( signum() >= 0) {
            return this;
        } else {
            return this.negate();
        }
    }

    /** Return the maximum of this integer and the argument.
     */
    public JMLInfiniteInteger max(JMLInfiniteInteger n) {
        if (compareTo(n) >= 0) {
            return this;
        } else {
            return n;
        }
    }

    public JMLInfiniteInteger min(JMLInfiniteInteger n) {
        if (compareTo(n) <= 0) {
            return this;
        } else {
            return n;
        }
    }
}

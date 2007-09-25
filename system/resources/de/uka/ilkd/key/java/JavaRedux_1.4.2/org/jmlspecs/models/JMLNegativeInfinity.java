// @(#)$Id: JMLNegativeInfinity.java 1.2 Tue, 17 May 2005 14:57:40 +0200 engelc $

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

/** Negative Infinity.
 *
 * @version $Revision: 1.2 $
 * @author Gary T. Leavens
 * @see JMLPositiveInfinity
 */
//-@ immutable
public /*@ pure @*/ class JMLNegativeInfinity extends JMLInfiniteIntegerClass {

    //@ public represents is_infinite <- true;
    //@ public represents sign <- -1;

    //@ public invariant_redundantly is_infinite;
    //@ public invariant_redundantly sign == -1;

    //@ public invariant_redundantly !nonnegative;

    /** Initialize this object.
     */
    public JMLNegativeInfinity() {}

    /** Return the sign of this integer.
     */
    public int signum() { return -1; }

    /** Return false.
     */
    public boolean isFinite() { return false; }

    /** Throw an ArithmeticException.
     */
    public BigInteger finiteValue() throws ArithmeticException {
        throw new ArithmeticException();
    }

    /** Compare this to the given integer, returning a comparison code.
     */
    public int compareTo(JMLInfiniteInteger n) {
        if (n instanceof JMLNegativeInfinity) {
            return 0;
        } else {
            return -1;
        }
    }

    /** Compare this to o, returning a comparison code.
     *  @param o the object this is compared to.
     *  @exception ClassCastException when o is not
     *             a JMLInfiniteInteger or a BigInteger.
     */
    public int compareTo(Object o) throws ClassCastException { 
        if (o == null) {
            throw new NullPointerException();
        } else if (o instanceof JMLNegativeInfinity) {
            return 0;
        } else if (o instanceof JMLInfiniteInteger
                   || o instanceof BigInteger) {
            return -1;
        } else {
            throw new ClassCastException();
        }
    }

    /** Return a hash code for this object.
     */
    public int hashCode() { return Integer.MIN_VALUE; }

    /** Return positive infinity.
     */
    public JMLInfiniteInteger negate() {
        return new JMLPositiveInfinity();
    }

    /** Return the sum of this integer and the argument.
     */
    public JMLInfiniteInteger add(JMLInfiniteInteger n) {
        if (n instanceof JMLPositiveInfinity) {
            return JMLFiniteInteger.ZERO;
        } else {
            return this;
        }
    }

    /** Return the difference between this integer and the argument.
     */
    public JMLInfiniteInteger subtract(JMLInfiniteInteger n) {
        if (n instanceof JMLNegativeInfinity) {
            return JMLFiniteInteger.ZERO;
        } else {
            return this;
        }
    }

    /** Return the product of this integer and the argument.
     */
    public JMLInfiniteInteger multiply(JMLInfiniteInteger n) {
        if (n.signum() == 0) {
            return JMLFiniteInteger.ZERO;
        } else if (n.signum() == -1) {
            return new JMLPositiveInfinity();
        } else {
            return this;
        }
    }

    /** Return the quotient of this integer divided by the argument.
     */
    public JMLInfiniteInteger divide(JMLInfiniteInteger n)
        throws ArithmeticException {
        if (n.signum() == 0) {
            throw new ArithmeticException("division by zero");
        } else if (n instanceof JMLNegativeInfinity) {
            return JMLFiniteInteger.ONE;
        } else if (n instanceof JMLPositiveInfinity) {
            return JMLFiniteInteger.ONE.negate();
        } else if (n.signum() == -1) {
            return new JMLPositiveInfinity();
        } else {
            return this;
        }
    }

    /** Return the remainder of this integer divided by the argument.
     */
    public JMLInfiniteInteger remainder(JMLInfiniteInteger n)
        throws ArithmeticException {
        if (n.signum() == 0) {
            throw new ArithmeticException("can't take remainder by zero");
        } else {
            return JMLFiniteInteger.ZERO;
        }
    }

    /** Return this integer modulo the argument.
     */
    public JMLInfiniteInteger mod(JMLInfiniteInteger n)
        throws ArithmeticException {
        if (n.signum() <= 0) {
            throw new ArithmeticException("can't mod by zero"
                                          + " or negative number");
        } else {
            return JMLFiniteInteger.ZERO;
        }
    }

    /** Return this integer raised to the argument's power.
     */
    public JMLInfiniteInteger pow(int n) throws ArithmeticException {
        if (n < 0) {
            throw new ArithmeticException();
        } else if (n == 0) {
            return JMLFiniteInteger.ONE;
        } else if (n % 2 == 1) {
            return this;
        } else {
            return this.negate();
        }
    }

    /** Return this integer approximated by a double.
     */
    public double doubleValue() { return Double.NEGATIVE_INFINITY; }

    /** Return this integer approximated by a float.
     */
    public float floatValue() { return Float.NEGATIVE_INFINITY; }

    /** Return the string "-Infinity".
     */
    public String toString() { return "-Infinity"; }

    /** Return the string "-Infinity".
     */
    public String toString(int radix) { return toString(); }
}

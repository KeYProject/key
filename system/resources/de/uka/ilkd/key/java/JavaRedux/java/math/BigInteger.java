// Copyright (C) 2001 Iowa State University

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

package java.math;

//import java.util.Random;

/** JML's specification of java.math.BigInteger.
 * Taken from jmlspecs repository and modified to be usable with KeY.
 * @version $Revision: 1388 $ KeY
 * @author David R. Cok
 * @author Gary T. Leavens
 * @author Daniel Bruns
 */
public /*@ pure @*/ class BigInteger extends java.lang.Number implements java.lang.Comparable {

  
    public BigInteger(/*@ non_null @*/ byte[] val);

    public BigInteger(int signum, /*@ non_null @*/ byte[] magnitude);

    public BigInteger(String val, int radix);

    BigInteger(char[] val);

 
    public BigInteger(String val);

    //@ pure
    public BigInteger(int numBits, Random rnd);

    //@ pure
    public BigInteger(int bitLength, int certainty, Random rnd);

    public static /*@ pure @*/ BigInteger probablePrime(int bitLength,
                                                          Random rnd);

//    boolean primeToCertainty(int certainty, java.util.Random r); // CHANGED in 1.6

    private static int jacobiSymbol(int p, BigInteger n);
    //Static Factory Methods

    public static /*@ pure @*/ BigInteger valueOf(long val);

    public static final BigInteger ZERO;
    public static final BigInteger ONE;

    //@ public invariant ZERO != null && ZERO.equals(valueOf(0L));
    //@ public invariant ONE != null && ONE.equals(valueOf(1L));

    // Arithmetic Operations

    public BigInteger add(BigInteger val);

    public BigInteger subtract(BigInteger val);
    
    public BigInteger multiply(BigInteger val);

    public BigInteger divide(BigInteger val);

    //@ ensures \result[0].equals(divide(val));
    //@ ensures \result[1].equals(remainder(val));
    public BigInteger[] divideAndRemainder(BigInteger val);

    public BigInteger remainder(BigInteger val);

    public BigInteger pow(int exponent);

    public BigInteger gcd(BigInteger val);

    static void primitiveRightShift(int[] a, int len, int n);

    static void primitiveLeftShift(int[] a, int len, int n);

    public BigInteger abs();

    public BigInteger negate();

    public int signum();

    // Modular Arithmetic Operations

    public BigInteger mod(BigInteger m);

    public BigInteger modPow(BigInteger exponent, BigInteger m);

    static int[] bnExpModThreshTable;

    static int mulAdd(int[] out, int[] in, int offset, int len, int k);

    static int addOne(int[] a, int offset, int mlen, int carry);

    public BigInteger modInverse(BigInteger m);

    // Shift Operations

    public BigInteger shiftLeft(int n);

    public BigInteger shiftRight(int n);

    int[] javaIncrement(int[] val);

    // Bitwise Operations

    public BigInteger and(BigInteger val);

    public BigInteger or(BigInteger val);

    public BigInteger xor(BigInteger val);

    public BigInteger not();

    public BigInteger andNot(BigInteger val);

    // Single Bit Operations

    public boolean testBit(int n);

    public BigInteger setBit(int n);

    public BigInteger clearBit(int n);

    public BigInteger flipBit(int n);

    public int getLowestSetBit();

    // Miscellaneous Bit Operations

    public int bitLength();

    public int bitCount();


    // Primality Testing

    public boolean isProbablePrime(int certainty);

    // Comparison Operations

    public int compareTo(BigInteger val);

    public /*@ pure @*/ boolean equals(Object x);

    public BigInteger min(BigInteger val);

    public BigInteger max(BigInteger val);

    // Hash Function

    public int hashCode();

    public String toString(int radix);

    public String toString();

    public byte[] toByteArray();

    public int intValue();

    public long longValue();

    public float floatValue();

    public double doubleValue();

}

// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2015 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package org.key_project.util.bitops;

import java.util.ArrayList;
import java.util.BitSet;

/**
 * Represents a non-negative number with access to single bits; the length of
 * the bit set is fixed. Comparable to {@link BitSet} with fixed length. Objects
 * of this class are immutable.
 *
 * @author Dominic Scheurer
 */
public class ImmutableFixedLengthBitSet {

    private boolean[] bitSet = null;
    private int value = -1;

    /**
     * Constructs a new {@link ImmutableFixedLengthBitSet} for the given length.
     * All bits are set to zero (so the {@link ImmutableFixedLengthBitSet}
     * represents the number 0).
     *
     * @param length
     *            The length of the new {@link ImmutableFixedLengthBitSet}.
     */
    public ImmutableFixedLengthBitSet(int length) {
        this.bitSet = new boolean[length];
        this.value = 0;
    }

    /**
     * Constructs a new {@link ImmutableFixedLengthBitSet} from an explicit
     * internal representation and value. Note: It is not checked that the value
     * really faithfully represents the bitSet, so callers are responsible to
     * make sure that this property holds.
     *
     * @param bitSet
     *            The new bit set.
     * @param value
     *            The value for bitSet.
     */
    private ImmutableFixedLengthBitSet(boolean[] bitSet, int value) {
        this.bitSet = bitSet;
        this.value = value;
    }

    /**
     * @return The integer value represented by this
     *         {@link ImmutableFixedLengthBitSet}.
     */
    public/* @ pure @ */int getValue() {
        if (value > -1) {
            return value;
        }

        int result = 0;

        for (int i = 0; i < bitSet.length; i++) {
            if (bitSet[i]) {
                result |= intPow(2, i);
            }
        }

        return result;
    }

    /**
     * Sets this {@link ImmutableFixedLengthBitSet} to the given value.
     *
     * @param value
     *            Value to set the {@link ImmutableFixedLengthBitSet} to.
     */
    public ImmutableFixedLengthBitSet setToValue(int value) {
        assert value < intPow(2, bitSet.length) : "Value to high for this bit set.";
        assert value > -1 : "Only non-negative values are allowed.";

        boolean[] newBitSet = new boolean[this.bitSet.length];
        for (int i = 0; i < newBitSet.length; i++) {
            int bit = intPow(2, i);
            newBitSet[i] = (value & bit) != 0;
        }

        return new ImmutableFixedLengthBitSet(newBitSet, value);
    }

    /**
     * Returns a new {@link ImmutableFixedLengthBitSet} with a value incremented
     * by one compared to this {@link ImmutableFixedLengthBitSet}.
     */
    public ImmutableFixedLengthBitSet inc() {
        return setToValue(getValue() + 1);
    }

    /**
     * @return The number of bits in the {@link ImmutableFixedLengthBitSet} set
     *         to zero.
     */
    public/* @ pure @ */int getNumOfZeroBits() {
        int result = 0;

        for (int i = 0; i < bitSet.length; i++) {
            if (!bitSet[i]) {
                result++;
            }
        }

        return result;
    }

    /**
     * @return A list of all non-zero positions in the
     *         {@link ImmutableFixedLengthBitSet}.
     */
    public ArrayList<Integer> getNonzeroPositions() {
        ArrayList<Integer> result = new ArrayList<Integer>();
        for (int i = 0; i < bitSet.length; i++) {
            if (bitSet[i]) {
                result.add(i);
            }
        }

        return result;
    }

    /*
     * (non-Javadoc)
     * 
     * @see java.lang.Object#toString()
     */
    @Override
    public String toString() {
        StringBuffer result = new StringBuffer();

        result.append(getValue()).append(" [");

        for (boolean bit : bitSet) {
            result.append(bit ? "1" : 0);
            result.append(",");
        }

        result.deleteCharAt(result.length() - 1);
        result.append("]");

        return result.toString();
    }

    /**
     * Power function for integers.
     *
     * @param a
     *            The base.
     * @param b
     *            The exponent.
     * @return a^b.
     */
    private static int intPow(int a, int b) {
        return (int) Math.round(Math.pow(a, b));
    }

}

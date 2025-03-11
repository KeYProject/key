/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.util.testcase.bitops;

import java.util.ArrayList;

import org.key_project.util.bitops.ImmutableFixedLengthBitSet;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.fail;

/**
 * Test case for {@link ImmutableFixedLengthBitSet}.
 *
 * @author Dominic Scheurer
 */
public class TestFixedLengthBitSet {
    @Test
    public void testNumOfZeroBits() {
        ImmutableFixedLengthBitSet lbn = new ImmutableFixedLengthBitSet(4);

        // 0000
        assertEquals(4, lbn.getNumOfZeroBits());

        // 1011
        lbn = lbn.setToValue(11);
        assertEquals(1, lbn.getNumOfZeroBits());

        // 1100
        lbn = lbn.setToValue(12);
        assertEquals(2, lbn.getNumOfZeroBits());

        // 1000
        lbn = lbn.setToValue(8);
        assertEquals(3, lbn.getNumOfZeroBits());

        // 1111
        lbn = lbn.setToValue(15);
        assertEquals(0, lbn.getNumOfZeroBits());
    }

    @Test
    public void testNonzeroPositions() {
        ImmutableFixedLengthBitSet lbn = new ImmutableFixedLengthBitSet(4);

        // 0000
        ArrayList<Integer> expected = new ArrayList<>();
        assertEquals(expected, lbn.getNonzeroPositions());

        // 1011
        lbn = lbn.setToValue(11);
        expected.add(0);
        expected.add(1);
        expected.add(3);
        assertEquals(expected, lbn.getNonzeroPositions());

        // 1100
        lbn = lbn.setToValue(12);
        expected = new ArrayList<>();
        expected.add(2);
        expected.add(3);
        assertEquals(expected, lbn.getNonzeroPositions());

        // 1000
        lbn = lbn.setToValue(8);
        expected = new ArrayList<>();
        expected.add(3);
        assertEquals(expected, lbn.getNonzeroPositions());

        // 1111
        lbn = lbn.setToValue(15);
        expected = new ArrayList<>();
        expected.add(0);
        expected.add(1);
        expected.add(2);
        expected.add(3);
        assertEquals(expected, lbn.getNonzeroPositions());
    }

    @Test
    public void testSetTooLargeNumber() {
        ImmutableFixedLengthBitSet lbn = new ImmutableFixedLengthBitSet(4);

        try {
            lbn.setToValue(16);
        } catch (AssertionError e) {
            return;
        }

        fail("Too large number should induce an assertion violation.");
    }

    @Test
    public void testnegativeNumber() {
        ImmutableFixedLengthBitSet lbn = new ImmutableFixedLengthBitSet(4);

        try {
            lbn.setToValue(-1);
        } catch (AssertionError e) {
            return;
        }

        fail("Negative number should induce an assertion violation.");
    }

    @Test
    public void testConversion() {
        ImmutableFixedLengthBitSet lbn = new ImmutableFixedLengthBitSet(4);

        // 1011
        lbn = lbn.setToValue(11);
        assertEquals(11, lbn.getValue());

        // 1100
        lbn = lbn.setToValue(12);
        assertEquals(12, lbn.getValue());

        // 1000
        lbn = lbn.setToValue(8);
        assertEquals(8, lbn.getValue());
    }

    @Test
    public void testIncrementation() {
        ImmutableFixedLengthBitSet lbn = new ImmutableFixedLengthBitSet(4);
        assertEquals(0, lbn.getValue());

        for (int i = 0; i < 15; i++) {
            assertEquals(i, lbn.getValue());
            lbn = lbn.inc();
        }

        assertEquals(15, lbn.getValue());
    }

}

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

package org.key_project.util.testcase.bitops;

import java.util.ArrayList;

import junit.framework.TestCase;

import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.ExpectedException;
import org.key_project.util.bitops.ImmutableFixedLengthBitSet;

/**
 * Test case for {@link ImmutableFixedLengthBitSet}.
 *
 * @author Dominic Scheurer
 */
public class TestFixedLengthBitSet extends TestCase {
    @Rule
    public ExpectedException thrown = ExpectedException.none();

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
        ArrayList<Integer> expected = new ArrayList<Integer>(); 
        assertEquals(expected, lbn.getNonzeroPositions());

        // 1011
        lbn = lbn.setToValue(11);
        expected.add(0);
        expected.add(1);
        expected.add(3);
        assertEquals(expected, lbn.getNonzeroPositions());

        // 1100
        lbn = lbn.setToValue(12);
        expected = new ArrayList<Integer>(); 
        expected.add(2);
        expected.add(3);
        assertEquals(expected, lbn.getNonzeroPositions());

        // 1000
        lbn = lbn.setToValue(8);
        expected = new ArrayList<Integer>(); 
        expected.add(3);
        assertEquals(expected, lbn.getNonzeroPositions());

        // 1111
        lbn = lbn.setToValue(15);
        expected = new ArrayList<Integer>(); 
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
        }
        catch (AssertionError e) {
            return;
        }

        fail("Too large number should induce an assertion violation.");
    }

    @Test
    public void testnegativeNumber() {
        ImmutableFixedLengthBitSet lbn = new ImmutableFixedLengthBitSet(4);

        try {
            lbn.setToValue(-1);
        }
        catch (AssertionError e) {
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

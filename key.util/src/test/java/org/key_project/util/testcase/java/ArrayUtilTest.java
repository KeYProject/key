/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.util.testcase.java;

import java.util.function.Predicate;

import org.key_project.util.java.ArrayUtil;
import org.key_project.util.java.StringUtil;

import org.jspecify.annotations.Nullable;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Tests for {@link ArrayUtil}
 *
 * @author Martin Hentschel
 */
public class ArrayUtilTest {
    @Test
    public void testInsert() {
        @Nullable
        String[] array = { "A", "B", "C" };
        // Test possible indices
        assertArray(ArrayUtil.insert(array, "X", 0), "X", "A", "B", "C");
        assertArray(ArrayUtil.insert(array, "X", 1), "A", "X", "B", "C");
        assertArray(ArrayUtil.insert(array, "X", 2), "A", "B", "X", "C");
        assertArray(ArrayUtil.insert(array, "X", 3), "A", "B", "C", "X");
        // Test null element
        assertArray(ArrayUtil.insert(array, null, 1), "A", null, "B", "C");
        // Test invalid indices
        try {
            ArrayUtil.insert(array, "X", -1);
            fail();
        } catch (ArrayIndexOutOfBoundsException e) {
        }
        try {
            ArrayUtil.insert(array, "X", 4);
            fail();
        } catch (ArrayIndexOutOfBoundsException e) {
        }
    }

    @SuppressWarnings("unchecked")
    private <T extends @Nullable Object> void assertArray(T[] current, T... expected) {
        assertNotNull(current);
        assertEquals(current.length, expected.length);
        for (int i = 0; i < current.length; i++) {
            assertEquals(current[i], expected[i]);
        }
    }

    /**
     * Tests for {@link ArrayUtil#search(Object[], Predicate)}.
     */
    @Test
    public void testSearch() {
        @Nullable
        String[] array = { "A", "B", "C", "D" };
        assertEquals("A", ArrayUtil.<@Nullable String>search(array, "A"::equals));
        assertEquals("B", ArrayUtil.<@Nullable String>search(array, "B"::equals));
        assertEquals("C", ArrayUtil.<@Nullable String>search(array, "C"::equals));
        assertEquals("D", ArrayUtil.<@Nullable String>search(array, "D"::equals));
        assertNull(ArrayUtil.<@Nullable String>search(array, "E"::equals));
    }

    /**
     * Tests {@link ArrayUtil#isEmpty(Object[])}
     */
    @Test
    public void testIsEmpty() {
        assertTrue(ArrayUtil.isEmpty(new String[] {}));
        assertFalse(ArrayUtil.isEmpty(new String[] { "A" }));
        assertFalse(ArrayUtil.isEmpty(new String[] { null }));
        assertFalse(ArrayUtil.isEmpty(new String[] { "A", "B" }));
    }

    /**
     * Tests {@link ArrayUtil#toString(int[], String)}
     */
    @Test
    public void testToString_int_String() {
        assertEquals(StringUtil.EMPTY_STRING, ArrayUtil.toString(new int[] {}, ";"));
        assertEquals("1", ArrayUtil.toString(new int[] { 1 }, ";"));
        assertEquals("1;2", ArrayUtil.toString(new int[] { 1, 2 }, ";"));
        assertEquals("1;2;3", ArrayUtil.toString(new int[] { 1, 2, 3 }, ";"));
    }

    /**
     * Tests {@link ArrayUtil#toString(int[])}
     */
    @Test
    public void testToString_int() {
        assertEquals(StringUtil.EMPTY_STRING, ArrayUtil.toString(new int[] {}));
        assertEquals("1", ArrayUtil.toString(new int[] { 1 }));
        assertEquals("1, 2", ArrayUtil.toString(new int[] { 1, 2 }));
        assertEquals("1, 2, 3", ArrayUtil.toString(new int[] { 1, 2, 3 }));
    }

    /**
     * Tests {@link ArrayUtil#toString(Object[], String)}
     */
    @Test
    public void testToString_Object_String() {
        assertEquals(StringUtil.EMPTY_STRING, ArrayUtil.toString(new String[] {}, ";"));
        assertEquals("A", ArrayUtil.toString(new String[] { "A" }, ";"));
        assertEquals("A;B", ArrayUtil.toString(new String[] { "A", "B" }, ";"));
        assertEquals("A;B;null", ArrayUtil.toString(new String[] { "A", "B", null }, ";"));
        assertEquals("A;B;null;D", ArrayUtil.toString(new String[] { "A", "B", null, "D" }, ";"));
    }

    /**
     * Tests {@link ArrayUtil#toString(Object[])}
     */
    @Test
    public void testToString_Object() {
        assertEquals(StringUtil.EMPTY_STRING, ArrayUtil.toString(new String[] {}));
        assertEquals("A", ArrayUtil.toString(new String[] { "A" }));
        assertEquals("A, B", ArrayUtil.toString(new String[] { "A", "B" }));
        assertEquals("A, B, null", ArrayUtil.toString(new String[] { "A", "B", null }));
        assertEquals("A, B, null, D", ArrayUtil.toString(new String[] { "A", "B", null, "D" }));
    }

    /**
     * Tests {@link ArrayUtil#remove(Object[], Object)}.
     */
    @Test
    public void testRemove() {
        // Test remove on array
        @Nullable
        String[] array = new @Nullable String[] { "A", "B", "C", null, "D", null, null, "C", "A" };
        array = ArrayUtil.remove(array, "B"); // Remove B
        assertArrayEquals(array, "A", "C", null, "D", null, null, "C", "A");
        array = ArrayUtil.remove(array, "B"); // Remove B again
        assertArrayEquals(array, "A", "C", null, "D", null, null, "C", "A");
        array = ArrayUtil.remove(array, "D"); // Remove D
        assertArrayEquals(array, "A", "C", null, null, null, "C", "A");
        array = ArrayUtil.remove(array, "C"); // Remove D
        assertArrayEquals(array, "A", null, null, null, "A");
        array = ArrayUtil.remove(array, null); // Remove null
        assertArrayEquals(array, "A", "A");
        array = ArrayUtil.remove(array, "INVALID"); // Remove invalid
        assertArrayEquals(array, "A", "A");
        array = ArrayUtil.remove(array, "A"); // Remove A
        assertArrayEquals(array);
        array = ArrayUtil.remove(array, "A"); // Remove A
        assertArrayEquals(array);
    }

    /**
     * Makes sure that the given array contains all values.
     *
     * @param array The array.
     * @param expectedValues The expected values.
     */
    @SuppressWarnings("unchecked")
    protected <T> void assertArrayEquals(T[] array, T... expectedValues) {
        assertNotNull(array);
        assertEquals(expectedValues.length, array.length);
        for (int i = 0; i < expectedValues.length; i++) {
            assertEquals(expectedValues[i], array[i]);
        }
    }

    /**
     * Tests {@link ArrayUtil#addAll(Object[], Object[])}
     */
    @Test
    public void testAddAll() {
        String[] first = new String[] { "A", "B", "C" };
        String[] second = new String[] { "D", "E" };
        @Nullable
        String[] combined = ArrayUtil.addAll(first, second);
        assertEquals(5, combined.length);
        assertEquals("A", combined[0]);
        assertEquals("B", combined[1]);
        assertEquals("C", combined[2]);
        assertEquals("D", combined[3]);
        assertEquals("E", combined[4]);
    }

    /**
     * Tests {@link ArrayUtil#addAll(Object[], Object[], Class)}
     */
    @Test
    public void testAddAll_newType() {
        String[] first = new String[] { "A", "B", "C" };
        String[] second = new String[] { "D", "E" };
        @Nullable
        Object[] combined = ArrayUtil.addAll(first, second, Object.class);
        assertEquals(Object.class, combined.getClass().getComponentType());
        assertEquals(5, combined.length);
        assertEquals("A", combined[0]);
        assertEquals("B", combined[1]);
        assertEquals("C", combined[2]);
        assertEquals("D", combined[3]);
        assertEquals("E", combined[4]);
    }

    /**
     * Tests {@link ArrayUtil#add(int[], int)}
     */
    @Test
    public void testAdd_int() {
        // Test empty array
        int[] array = new int[] {};
        int[] result = ArrayUtil.add(array, 1);
        assertNotNull(result);
        assertEquals(1, result.length);
        assertEquals(1, result[0]);
        // Test array with one element
        array = new int[] { 1 };
        result = ArrayUtil.add(array, 2);
        assertNotNull(result);
        assertEquals(2, result.length);
        assertEquals(1, result[0]);
        assertEquals(2, result[1]);
        // Test array with two elements
        array = new int[] { 1, 2 };
        result = ArrayUtil.add(array, 3);
        assertNotNull(result);
        assertEquals(3, result.length);
        assertEquals(1, result[0]);
        assertEquals(2, result[1]);
        assertEquals(3, result[2]);
        // Test array with three elements
        array = new int[] { 1, 2, 3 };
        result = ArrayUtil.add(array, 4);
        assertNotNull(result);
        assertEquals(4, result.length);
        assertEquals(1, result[0]);
        assertEquals(2, result[1]);
        assertEquals(3, result[2]);
        assertEquals(4, result[3]);
    }

    /**
     * Tests {@link ArrayUtil#add(Object[], Object)}
     */
    @Test
    public void testAdd_Object() {
        // Test empty array
        @Nullable
        String[] array = new String[] {};
        @Nullable
        String[] result = ArrayUtil.add(array, "A");
        assertNotNull(result);
        assertEquals(1, result.length);
        assertEquals("A", result[0]);
        // Test array with one element
        array = new String[] { "A" };
        result = ArrayUtil.add(array, "B");
        assertNotNull(result);
        assertEquals(2, result.length);
        assertEquals("A", result[0]);
        assertEquals("B", result[1]);
        // Test array with two elements
        array = new String[] { "A", "B" };
        result = ArrayUtil.add(array, "C");
        assertNotNull(result);
        assertEquals(3, result.length);
        assertEquals("A", result[0]);
        assertEquals("B", result[1]);
        assertEquals("C", result[2]);
        // Test array with three elements
        array = new String[] { "A", "B", "C" };
        result = ArrayUtil.add(array, "D");
        assertNotNull(result);
        assertEquals(4, result.length);
        assertEquals("A", result[0]);
        assertEquals("B", result[1]);
        assertEquals("C", result[2]);
        assertEquals("D", result[3]);
        // Test null new element
        array = new String[] { "A", "B", "C" };
        result = ArrayUtil.add(array, null);
        assertNotNull(result);
        assertEquals(4, result.length);
        assertEquals("A", result[0]);
        assertEquals("B", result[1]);
        assertEquals("C", result[2]);
        assertNull(result[3]);
    }

    /**
     * Tests {@link ArrayUtil#contains(Object[], Object)}
     */
    @Test
    public void testContains() {
        String[] array = { "A", "B", "C" };
        assertFalse(ArrayUtil.contains(array, null));
        assertTrue(ArrayUtil.contains(array, "A"));
        assertTrue(ArrayUtil.contains(array, "B"));
        assertTrue(ArrayUtil.contains(array, "C"));
        assertFalse(ArrayUtil.contains(array, "D"));
        @Nullable
        String[] arrayWithNull = { "A", "B", null, "D" };
        assertTrue(ArrayUtil.contains(arrayWithNull, null));
        assertTrue(ArrayUtil.contains(arrayWithNull, "A"));
        assertTrue(ArrayUtil.contains(arrayWithNull, "B"));
        assertFalse(ArrayUtil.contains(arrayWithNull, "C"));
        assertTrue(ArrayUtil.contains(arrayWithNull, "D"));
        assertFalse(ArrayUtil.contains(arrayWithNull, "E"));
        String[] arrayWithDoubleElements = { "B", "A", "C", "B", "C" };
        assertFalse(ArrayUtil.contains(arrayWithDoubleElements, null));
        assertTrue(ArrayUtil.contains(arrayWithDoubleElements, "A"));
        assertTrue(ArrayUtil.contains(arrayWithDoubleElements, "B"));
        assertTrue(ArrayUtil.contains(arrayWithDoubleElements, "C"));
        assertFalse(ArrayUtil.contains(arrayWithDoubleElements, "D"));
    }

    /**
     * Tests {@link ArrayUtil#indexOf(Object[], Object)}
     */
    @Test
    public void testIndexOf() {
        String[] array = { "A", "B", "C" };
        assertEquals(-1, ArrayUtil.indexOf(array, null));
        assertEquals(0, ArrayUtil.indexOf(array, "A"));
        assertEquals(1, ArrayUtil.indexOf(array, "B"));
        assertEquals(2, ArrayUtil.indexOf(array, "C"));
        assertEquals(-1, ArrayUtil.indexOf(array, "D"));
        @Nullable
        String[] arrayWithNull = { "A", "B", null, "D" };
        assertEquals(2, ArrayUtil.indexOf(arrayWithNull, null));
        assertEquals(0, ArrayUtil.indexOf(arrayWithNull, "A"));
        assertEquals(1, ArrayUtil.indexOf(arrayWithNull, "B"));
        assertEquals(-1, ArrayUtil.indexOf(arrayWithNull, "C"));
        assertEquals(3, ArrayUtil.indexOf(arrayWithNull, "D"));
        assertEquals(-1, ArrayUtil.indexOf(arrayWithNull, "E"));
        String[] arrayWithDoubleElements = { "B", "A", "C", "B", "C" };
        assertEquals(-1, ArrayUtil.indexOf(arrayWithDoubleElements, null));
        assertEquals(1, ArrayUtil.indexOf(arrayWithDoubleElements, "A"));
        assertEquals(0, ArrayUtil.indexOf(arrayWithDoubleElements, "B"));
        assertEquals(2, ArrayUtil.indexOf(arrayWithDoubleElements, "C"));
        assertEquals(-1, ArrayUtil.indexOf(arrayWithDoubleElements, "D"));
    }
}

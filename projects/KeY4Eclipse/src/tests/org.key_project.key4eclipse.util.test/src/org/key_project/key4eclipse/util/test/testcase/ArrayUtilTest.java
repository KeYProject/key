/*******************************************************************************
 * Copyright (c) 2011 Martin Hentschel.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Martin Hentschel - initial API and implementation
 *******************************************************************************/

package org.key_project.key4eclipse.util.test.testcase;

import junit.framework.TestCase;

import org.junit.Test;
import org.key_project.key4eclipse.util.java.ArrayUtil;

/**
 * Tests for {@link ArrayUtil}
 * @author Martin Hentschel
 */
public class ArrayUtilTest extends TestCase {
    /**
     * Tests {@link ArrayUtil#addAll(Object[], Object[])}
     */
    @Test
    public void testAddAll() {
        String[] first = new String[] {"A", "B", "C"};
        String[] second = new String[] {"D", "E"};
        // Test first parameter null
        String[] combined = ArrayUtil.addAll(null, second);
        assertEquals(2, combined.length);
        assertEquals("D", combined[0]);
        assertEquals("E", combined[1]);
        // Test second parameter null
        combined = ArrayUtil.addAll(first, null);
        assertEquals(3, combined.length);
        assertEquals("A", combined[0]);
        assertEquals("B", combined[1]);
        assertEquals("C", combined[2]);
        // Test both parameter valid
        combined = ArrayUtil.addAll(first, second);
        assertEquals(5, combined.length);
        assertEquals("A", combined[0]);
        assertEquals("B", combined[1]);
        assertEquals("C", combined[2]);
        assertEquals("D", combined[3]);
        assertEquals("E", combined[4]);
        // Test both parameter null
        try {
            ArrayUtil.addAll(null, null);
            fail("Exception expected if both parameters are null.");
        }
        catch (IllegalArgumentException e) {
            assertEquals("Can not create an array if both paramters are null.", e.getMessage());
        }
    }
    
    /**
     * Tests {@link ArrayUtil#add(Object[], Object)}
     */
    @Test
    public void testAdd() {
        // Test null array
        String[] result = ArrayUtil.add(null, "A");
        assertNotNull(result);
        assertEquals(1, result.length);
        assertEquals("A", result[0]);
        // Test empty array
        String[] array = new String[] {};
        result = ArrayUtil.add(array, "A");
        assertNotNull(result);
        assertEquals(1, result.length);
        assertEquals("A", result[0]);
        // Test array with one element
        array = new String[] {"A"};
        result = ArrayUtil.add(array, "B");
        assertNotNull(result);
        assertEquals(2, result.length);
        assertEquals("A", result[0]);
        assertEquals("B", result[1]);
        // Test array with two elements
        array = new String[] {"A", "B"};
        result = ArrayUtil.add(array, "C");
        assertNotNull(result);
        assertEquals(3, result.length);
        assertEquals("A", result[0]);
        assertEquals("B", result[1]);
        assertEquals("C", result[2]);
        // Test array with three elements
        array = new String[] {"A", "B", "C"};
        result = ArrayUtil.add(array, "D");
        assertNotNull(result);
        assertEquals(4, result.length);
        assertEquals("A", result[0]);
        assertEquals("B", result[1]);
        assertEquals("C", result[2]);
        assertEquals("D", result[3]);
        // Test null new element
        array = new String[] {"A", "B", "C"};
        result = ArrayUtil.add(array, null);
        assertNotNull(result);
        assertEquals(4, result.length);
        assertEquals("A", result[0]);
        assertEquals("B", result[1]);
        assertEquals("C", result[2]);
        assertEquals(null, result[3]);
        // Test null new element on null array
        try {
            ArrayUtil.add(null, null);
            fail("Exception expected if both parameters are null.");
        }
        catch (IllegalArgumentException e) {
            assertEquals("Can not create an array if both paramters are null.", e.getMessage());
        }
    }
    
    /**
     * Tests {@link ArrayUtil#contains(Object[], Object)}
     */
    @Test
    public void testContains() {
       String[] array = {"A", "B", "C"};
       assertFalse(ArrayUtil.contains(array, null));
       assertFalse(ArrayUtil.contains(null, "A"));
       assertTrue(ArrayUtil.contains(array, "A"));
       assertTrue(ArrayUtil.contains(array, "B"));
       assertTrue(ArrayUtil.contains(array, "C"));
       assertFalse(ArrayUtil.contains(array, "D"));
       String[] arrayWithNull = {"A", "B", null, "D"};
       assertTrue(ArrayUtil.contains(arrayWithNull, null));
       assertFalse(ArrayUtil.contains(null, "A"));
       assertTrue(ArrayUtil.contains(arrayWithNull, "A"));
       assertTrue(ArrayUtil.contains(arrayWithNull, "B"));
       assertFalse(ArrayUtil.contains(arrayWithNull, "C"));
       assertTrue(ArrayUtil.contains(arrayWithNull, "D"));
       assertFalse(ArrayUtil.contains(arrayWithNull, "E"));
       String[] arrayWithDoubleElements = {"B", "A", "C", "B", "C"};
       assertFalse(ArrayUtil.contains(arrayWithDoubleElements, null));
       assertFalse(ArrayUtil.contains(null, "A"));
       assertTrue(ArrayUtil.contains(arrayWithDoubleElements, "A"));
       assertTrue(ArrayUtil.contains(arrayWithDoubleElements, "B"));
       assertTrue(ArrayUtil.contains(arrayWithDoubleElements, "C"));
       assertFalse(ArrayUtil.contains(arrayWithDoubleElements, "D"));
    }
}

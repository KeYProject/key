package org.key_project.util.test.testcase;

import java.util.Comparator;

import junit.framework.TestCase;

import org.junit.Test;
import org.key_project.util.java.ArrayUtil;
import org.key_project.util.java.ObjectUtil;
import org.key_project.util.java.StringUtil;

/**
 * Tests for {@link ArrayUtil}
 * @author Martin Hentschel
 */
public class ArrayUtilTest extends TestCase {
   /**
    * Tests {@link ArrayUtil#isEmpty(Object[])}
    */
   @Test
   public void testIsEmpty() {
      assertTrue(ArrayUtil.isEmpty(null));
      assertTrue(ArrayUtil.isEmpty(new String[] {}));
      assertFalse(ArrayUtil.isEmpty(new String[] {"A"}));
      assertFalse(ArrayUtil.isEmpty(new String[] {null}));
      assertFalse(ArrayUtil.isEmpty(new String[] {"A", "B"}));
   }
   
   /**
    * Tests {@link ArrayUtil#toString(int[], String)}
    */
   @Test
   public void testToString_int_String() {
      assertEquals(StringUtil.EMPTY_STRING, ArrayUtil.toString((int[])null, ";"));
      assertEquals(StringUtil.EMPTY_STRING, ArrayUtil.toString(new int[] {}, ";"));
      assertEquals("1", ArrayUtil.toString(new int[] {1}, ";"));
      assertEquals("1;2", ArrayUtil.toString(new int[] {1, 2}, ";"));
      assertEquals("1;2;3", ArrayUtil.toString(new int[] {1, 2, 3}, ";"));
      assertEquals("1null2null3", ArrayUtil.toString(new int[] {1, 2, 3}, null));
   }
   
   /**
    * Tests {@link ArrayUtil#toString(int[])}
    */
   @Test
   public void testToString_int() {
      assertEquals(StringUtil.EMPTY_STRING, ArrayUtil.toString((int[])null));
      assertEquals(StringUtil.EMPTY_STRING, ArrayUtil.toString(new int[] {}));
      assertEquals("1", ArrayUtil.toString(new int[] {1}));
      assertEquals("1, 2", ArrayUtil.toString(new int[] {1, 2}));
      assertEquals("1, 2, 3", ArrayUtil.toString(new int[] {1, 2, 3}));
   }
   
    /**
     * Tests {@link ArrayUtil#toString(Object[], String)}
     */
    @Test
    public void testToString_Object_String() {
        assertEquals(StringUtil.EMPTY_STRING, ArrayUtil.toString((String[])null, ";"));
        assertEquals(StringUtil.EMPTY_STRING, ArrayUtil.toString(new String[] {}, ";"));
        assertEquals("A", ArrayUtil.toString(new String[] {"A"}, ";"));
        assertEquals("A;B", ArrayUtil.toString(new String[] {"A", "B"}, ";"));
        assertEquals("A;B;null", ArrayUtil.toString(new String[] {"A", "B", null}, ";"));
        assertEquals("A;B;null;D", ArrayUtil.toString(new String[] {"A", "B", null, "D"}, ";"));
        assertEquals("AnullBnullnullnullD", ArrayUtil.toString(new String[] {"A", "B", null, "D"}, null));
    }
    
    /**
     * Tests {@link ArrayUtil#toString(Object[])}
     */
    @Test
    public void testToString_Object() {
        assertEquals(StringUtil.EMPTY_STRING, ArrayUtil.toString((String[])null));
        assertEquals(StringUtil.EMPTY_STRING, ArrayUtil.toString(new String[] {}));
        assertEquals("A", ArrayUtil.toString(new String[] {"A"}));
        assertEquals("A, B", ArrayUtil.toString(new String[] {"A", "B"}));
        assertEquals("A, B, null", ArrayUtil.toString(new String[] {"A", "B", null}));
        assertEquals("A, B, null, D", ArrayUtil.toString(new String[] {"A", "B", null, "D"}));
    }
    
    /**
     * Tests {@link ArrayUtil#remove(Object[], Object, Comparator)}.
     */
    @Test
    public void testRemove_Comparator() {
        Comparator<String> comparator = new Comparator<String>() {
            @Override
            public int compare(String o1, String o2) {
               if ("X".equals(o1) || "X".equals(o2)) {
                   return 0; // D is always true
               }
               else if ("B".equals(o1) && "B".equals(o2)) {
                   return Integer.MAX_VALUE; // B is false
               }
               else {
                   return ObjectUtil.equals(o1, o2) ? 0 : 1;
               }
            }
        };        
        // Test remove on array
        String[] array = new String[] {"A", "B", "C", null, "D", null, null, "C", "A"};
        array = ArrayUtil.remove(array, "B", comparator); // Remove B what is not possible 
        assertArrayEquals(array, "A", "B", "C", null, "D", null, null, "C", "A");
        array = ArrayUtil.remove(array, "B", comparator); // Remove B again is still not possible
        assertArrayEquals(array, "A", "B", "C", null, "D", null, null, "C", "A");
        array = ArrayUtil.remove(array, "D", comparator); // Remove D
        assertArrayEquals(array, "A", "B", "C", null, null, null, "C", "A");
        array = ArrayUtil.remove(array, "C", comparator); // Remove D
        assertArrayEquals(array, "A", "B", null, null, null, "A");
        array = ArrayUtil.remove(array, null, comparator); // Remove null
        assertArrayEquals(array, "A", "B", "A");
        array = ArrayUtil.remove(array, "INVALID", comparator); // Remove invalid
        assertArrayEquals(array, "A", "B", "A");
        array = ArrayUtil.remove(array, "A", comparator); // Remove A
        assertArrayEquals(array, "B");
        array = ArrayUtil.remove(array, "A", comparator); // Remove A
        assertArrayEquals(array, "B");
        // Test null array
        array = ArrayUtil.remove(null, "X", comparator);
        assertNull(array);
        // Test null comparator
        try {
            ArrayUtil.contains(new String[] {"A", "B"}, "A", null);
            fail("Comparison without a Comparator should not be possible");
        }
        catch (IllegalArgumentException e) {
            assertEquals("Comparator is null.", e.getMessage());
        }
    }
    
    /**
     * Tests {@link ArrayUtil#remove(Object[], Object)}.
     */
    @Test
    public void testRemove() {
        // Test remove on array
        String[] array = new String[] {"A", "B", "C", null, "D", null, null, "C", "A"};
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
        // Test null array
        array = ArrayUtil.remove(null, "X");
        assertNull(array);
    }
    
    /**
     * Makes sure that the given array contains all values.
     * @param array The array.
     * @param expectedValues The expected values.
     */
    protected void assertArrayEquals(String[] array, String... expectedValues) {
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
     * Tests {@link ArrayUtil#add(int[], int)}
     */
    @Test
    public void testAdd_int() {
        // Test null array
        int[] result = ArrayUtil.add(null, 1);
        assertNotNull(result);
        assertEquals(1, result.length);
        assertEquals(1, result[0]);
        // Test empty array
        int[] array = new int[] {};
        result = ArrayUtil.add(array, 1);
        assertNotNull(result);
        assertEquals(1, result.length);
        assertEquals(1, result[0]);
        // Test array with one element
        array = new int[] {1};
        result = ArrayUtil.add(array, 2);
        assertNotNull(result);
        assertEquals(2, result.length);
        assertEquals(1, result[0]);
        assertEquals(2, result[1]);
        // Test array with two elements
        array = new int[] {1, 2};
        result = ArrayUtil.add(array, 3);
        assertNotNull(result);
        assertEquals(3, result.length);
        assertEquals(1, result[0]);
        assertEquals(2, result[1]);
        assertEquals(3, result[2]);
        // Test array with three elements
        array = new int[] {1, 2, 3};
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
    
    /**
     * Tests {@link ArrayUtil#contains(Object[], Object, java.util.Comparator)}
     */
    @Test
    public void testContains_Comparator() {
       Comparator<String> comparator = new Comparator<String>() {
          @Override
          public int compare(String o1, String o2) {
             if ("X".equals(o1) || "X".equals(o2)) {
                 return 0; // D is always true
             }
             else if ("B".equals(o1) && "B".equals(o2)) {
                 return Integer.MAX_VALUE; // B is false
             }
             else {
                 return ObjectUtil.equals(o1, o2) ? 0 : 1;
             }
          }
       };
       String[] array = {"A", "B", "C"};
       assertFalse(ArrayUtil.contains(array, null, comparator));
       assertFalse(ArrayUtil.contains(null, "A", comparator));
       assertTrue(ArrayUtil.contains(array, "A", comparator));
       assertFalse(ArrayUtil.contains(array, "B", comparator));
       assertTrue(ArrayUtil.contains(array, "C", comparator));
       assertFalse(ArrayUtil.contains(array, "D", comparator));
       assertTrue(ArrayUtil.contains(array, "X", comparator));
       String[] arrayWithNull = {"A", "B", null, "D"};
       assertTrue(ArrayUtil.contains(arrayWithNull, null, comparator));
       assertFalse(ArrayUtil.contains(null, "A", comparator));
       assertTrue(ArrayUtil.contains(arrayWithNull, "A", comparator));
       assertFalse(ArrayUtil.contains(arrayWithNull, "B", comparator));
       assertFalse(ArrayUtil.contains(arrayWithNull, "C", comparator));
       assertTrue(ArrayUtil.contains(arrayWithNull, "D", comparator));
       assertFalse(ArrayUtil.contains(arrayWithNull, "E", comparator));
       assertTrue(ArrayUtil.contains(arrayWithNull, "X", comparator));
       String[] arrayWithDoubleElements = {"B", "A", "C", "B", "C"};
       assertFalse(ArrayUtil.contains(arrayWithDoubleElements, null, comparator));
       assertFalse(ArrayUtil.contains(null, "A", comparator));
       assertTrue(ArrayUtil.contains(arrayWithDoubleElements, "A", comparator));
       assertFalse(ArrayUtil.contains(arrayWithDoubleElements, "B", comparator));
       assertTrue(ArrayUtil.contains(arrayWithDoubleElements, "C", comparator));
       assertFalse(ArrayUtil.contains(arrayWithDoubleElements, "D", comparator));
       assertTrue(ArrayUtil.contains(arrayWithDoubleElements, "X", comparator));
       try {
           ArrayUtil.contains(array, "A", null);
           fail("Comparison without a Comparator should not be possible");
       }
       catch (IllegalArgumentException e) {
           assertEquals("Comparator is null.", e.getMessage());
       }
    }
    
    /**
     * Tests {@link ArrayUtil#indexOf(Object[], Object)}
     */
    @Test
    public void testIndexOf() {
       String[] array = {"A", "B", "C"};
       assertEquals(-1, ArrayUtil.indexOf(array, null));
       assertEquals(-1, ArrayUtil.indexOf(null, "A"));
       assertEquals(0, ArrayUtil.indexOf(array, "A"));
       assertEquals(1, ArrayUtil.indexOf(array, "B"));
       assertEquals(2, ArrayUtil.indexOf(array, "C"));
       assertEquals(-1, ArrayUtil.indexOf(array, "D"));
       String[] arrayWithNull = {"A", "B", null, "D"};
       assertEquals(2, ArrayUtil.indexOf(arrayWithNull, null));
       assertEquals(-1, ArrayUtil.indexOf(null, "A"));
       assertEquals(0, ArrayUtil.indexOf(arrayWithNull, "A"));
       assertEquals(1, ArrayUtil.indexOf(arrayWithNull, "B"));
       assertEquals(-1, ArrayUtil.indexOf(arrayWithNull, "C"));
       assertEquals(3, ArrayUtil.indexOf(arrayWithNull, "D"));
       assertEquals(-1, ArrayUtil.indexOf(arrayWithNull, "E"));
       String[] arrayWithDoubleElements = {"B", "A", "C", "B", "C"};
       assertEquals(-1, ArrayUtil.indexOf(arrayWithDoubleElements, null));
       assertEquals(-1, ArrayUtil.indexOf(null, "A"));
       assertEquals(1, ArrayUtil.indexOf(arrayWithDoubleElements, "A"));
       assertEquals(0, ArrayUtil.indexOf(arrayWithDoubleElements, "B"));
       assertEquals(2, ArrayUtil.indexOf(arrayWithDoubleElements, "C"));
       assertEquals(-1, ArrayUtil.indexOf(arrayWithDoubleElements, "D"));
    }
    
    /**
     * Tests {@link ArrayUtil#indexOf(Object[], Object, Comparator)}
     */
    @Test
    public void testIndexOf_Comparator() {
       Comparator<String> comparator = new Comparator<String>() {
          @Override
          public int compare(String o1, String o2) {
             if ("X".equals(o1) || "X".equals(o2)) {
                 return 0; // D is always true
             }
             else if ("B".equals(o1) && "B".equals(o2)) {
                 return Integer.MAX_VALUE; // B is false
             }
             else {
                 return ObjectUtil.equals(o1, o2) ? 0 : 1;
             }
          }
       };
       String[] array = {"A", "B", "C"};
       assertEquals(-1, ArrayUtil.indexOf(array, null, comparator));
       assertEquals(-1, ArrayUtil.indexOf(null, "A", comparator));
       assertEquals(0, ArrayUtil.indexOf(array, "A", comparator));
       assertEquals(-1, ArrayUtil.indexOf(array, "B", comparator));
       assertEquals(2, ArrayUtil.indexOf(array, "C", comparator));
       assertEquals(-1, ArrayUtil.indexOf(array, "D", comparator));
       assertEquals(0, ArrayUtil.indexOf(array, "X", comparator));
       String[] arrayWithNull = {"A", "B", null, "D"};
       assertEquals(2, ArrayUtil.indexOf(arrayWithNull, null, comparator));
       assertEquals(-1, ArrayUtil.indexOf(null, "A", comparator));
       assertEquals(0, ArrayUtil.indexOf(arrayWithNull, "A", comparator));
       assertEquals(-1, ArrayUtil.indexOf(arrayWithNull, "B", comparator));
       assertEquals(-1, ArrayUtil.indexOf(arrayWithNull, "C", comparator));
       assertEquals(3, ArrayUtil.indexOf(arrayWithNull, "D", comparator));
       assertEquals(-1, ArrayUtil.indexOf(arrayWithNull, "E", comparator));
       assertEquals(0, ArrayUtil.indexOf(arrayWithNull, "X", comparator));
       String[] arrayWithDoubleElements = {"B", "A", "C", "B", "C"};
       assertEquals(-1, ArrayUtil.indexOf(arrayWithDoubleElements, null, comparator));
       assertEquals(-1, ArrayUtil.indexOf(null, "A", comparator));
       assertEquals(1, ArrayUtil.indexOf(arrayWithDoubleElements, "A", comparator));
       assertEquals(-1, ArrayUtil.indexOf(arrayWithDoubleElements, "B", comparator));
       assertEquals(2, ArrayUtil.indexOf(arrayWithDoubleElements, "C", comparator));
       assertEquals(-1, ArrayUtil.indexOf(arrayWithDoubleElements, "D", comparator));
       assertEquals(0, ArrayUtil.indexOf(arrayWithDoubleElements, "X", comparator));
       try {
           ArrayUtil.indexOf(array, "A", null);
           fail("Comparison without a Comparator should not be possible");
       }
       catch (IllegalArgumentException e) {
           assertEquals("Comparator is null.", e.getMessage());
       }
    }
}

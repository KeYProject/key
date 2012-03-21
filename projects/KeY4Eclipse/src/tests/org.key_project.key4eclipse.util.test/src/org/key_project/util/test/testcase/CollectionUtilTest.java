package org.key_project.util.test.testcase;

import java.util.LinkedList;
import java.util.List;

import junit.framework.TestCase;

import org.junit.Test;
import org.key_project.util.java.CollectionUtil;
import org.key_project.util.java.IFilter;

/**
 * Tests for {@link CollectionUtil}.
 * @author Martin Hentschel
 */
public class CollectionUtilTest extends TestCase {
   /**
    * Tests {@link CollectionUtil#contains(Iterable, Object)}
    */
   @Test
   public void testContains() {
      // Create model
      List<String> list = new LinkedList<String>();
      list.add("A");
      list.add("B");
      list.add("C");
      list.add("D");
      // Test null parameter
      assertFalse(CollectionUtil.contains(null, "A"));
      assertFalse(CollectionUtil.contains(list, null));
      assertFalse(CollectionUtil.contains(null, null));
      // Test values
      assertTrue(CollectionUtil.contains(list, "A"));
      assertTrue(CollectionUtil.contains(list, "B"));
      assertTrue(CollectionUtil.contains(list, "C"));
      assertTrue(CollectionUtil.contains(list, "D"));
      assertFalse(CollectionUtil.contains(list, "E"));
      // Test valid null value
      list.add(null);
      assertTrue(CollectionUtil.contains(list, null));
   }
   
   /**
    * Tests for {@link CollectionUtil#search(Iterable, org.key_project.util.java.IFilter)}.
    */
   @Test
   public void testSearch() {
       List<String> collection = CollectionUtil.toList("A", "B", "C", "D");
       assertEquals("A", CollectionUtil.search(collection, new IFilter<String>() {
          @Override
          public boolean select(String element) {
             return "A".equals(element);
          }
       }));
       assertEquals("B", CollectionUtil.search(collection, new IFilter<String>() {
          @Override
          public boolean select(String element) {
             return "B".equals(element);
          }
       }));
       assertEquals("C", CollectionUtil.search(collection, new IFilter<String>() {
          @Override
          public boolean select(String element) {
             return "C".equals(element);
          }
       }));
       assertEquals("D", CollectionUtil.search(collection, new IFilter<String>() {
          @Override
          public boolean select(String element) {
             return "D".equals(element);
          }
       }));
       assertNull(CollectionUtil.search(collection, new IFilter<String>() {
          @Override
          public boolean select(String element) {
             return "E".equals(element);
          }
       }));
       assertNull(CollectionUtil.search(collection, null));
       assertNull(CollectionUtil.search(null, new IFilter<String>() {
          @Override
          public boolean select(String element) {
             return "E".equals(element);
          }
       }));
   }
    
   /**
    * Test for {@link CollectionUtil#removeComplete(java.util.Collection, Object)}
    */
   @Test
   public void testRemoveComplete() {
      List<String> collection = CollectionUtil.toList("A", "B", "C", "A", "A", "B", "A", "D");
      assertFalse(CollectionUtil.removeComplete(collection, null));
      assertEquals("A", collection.get(0));
      assertEquals("B", collection.get(1));
      assertEquals("C", collection.get(2));
      assertEquals("A", collection.get(3));
      assertEquals("A", collection.get(4));
      assertEquals("B", collection.get(5));
      assertEquals("A", collection.get(6));
      assertEquals("D", collection.get(7));
      assertFalse(CollectionUtil.removeComplete(null, "A"));
      assertEquals("A", collection.get(0));
      assertEquals("B", collection.get(1));
      assertEquals("C", collection.get(2));
      assertEquals("A", collection.get(3));
      assertEquals("A", collection.get(4));
      assertEquals("B", collection.get(5));
      assertEquals("A", collection.get(6));
      assertEquals("D", collection.get(7));
      assertFalse(CollectionUtil.removeComplete(collection, "X"));
      assertEquals("A", collection.get(0));
      assertEquals("B", collection.get(1));
      assertEquals("C", collection.get(2));
      assertEquals("A", collection.get(3));
      assertEquals("A", collection.get(4));
      assertEquals("B", collection.get(5));
      assertEquals("A", collection.get(6));
      assertEquals("D", collection.get(7));
      assertTrue(CollectionUtil.removeComplete(collection, "A"));
      assertEquals(4, collection.size());
      assertEquals("B", collection.get(0));
      assertEquals("C", collection.get(1));
      assertEquals("B", collection.get(2));
      assertEquals("D", collection.get(3));
      assertTrue(CollectionUtil.removeComplete(collection, "D"));
      assertEquals(3, collection.size());
      assertEquals("B", collection.get(0));
      assertEquals("C", collection.get(1));
      assertEquals("B", collection.get(2));
      assertTrue(CollectionUtil.removeComplete(collection, "B"));
      assertEquals(1, collection.size());
      assertEquals("C", collection.get(0));
      assertTrue(CollectionUtil.removeComplete(collection, "C"));
      assertEquals(0, collection.size());
   }
   
   /**
    * Test for {@link CollectionUtil#removeAll(java.util.Collection, Object...)}
    */
   @Test
   public void testRemoveAll() {
      List<String> collection = CollectionUtil.toList("A", "B", "C", "D", "E", "F", "G");
      assertFalse(CollectionUtil.removeAll(null, "A"));
      assertFalse(CollectionUtil.removeAll(collection, (String[])null));
      assertEquals(7, collection.size());
      assertEquals("A", collection.get(0));
      assertEquals("B", collection.get(1));
      assertEquals("C", collection.get(2));
      assertEquals("D", collection.get(3));
      assertEquals("E", collection.get(4));
      assertEquals("F", collection.get(5));
      assertEquals("G", collection.get(6));      
      assertFalse(CollectionUtil.removeAll(collection, "X"));
      assertEquals(7, collection.size());
      assertEquals("A", collection.get(0));
      assertEquals("B", collection.get(1));
      assertEquals("C", collection.get(2));
      assertEquals("D", collection.get(3));
      assertEquals("E", collection.get(4));
      assertEquals("F", collection.get(5));
      assertEquals("G", collection.get(6));      
      assertFalse(CollectionUtil.removeAll(collection, new String[] {"X", "Y"}));
      assertEquals(7, collection.size());
      assertEquals("A", collection.get(0));
      assertEquals("B", collection.get(1));
      assertEquals("C", collection.get(2));
      assertEquals("D", collection.get(3));
      assertEquals("E", collection.get(4));
      assertEquals("F", collection.get(5));
      assertEquals("G", collection.get(6));      
      assertTrue(CollectionUtil.removeAll(collection, "B"));
      assertEquals(6, collection.size());
      assertEquals("A", collection.get(0));
      assertEquals("C", collection.get(1));
      assertEquals("D", collection.get(2));
      assertEquals("E", collection.get(3));
      assertEquals("F", collection.get(4));
      assertEquals("G", collection.get(5));      
      assertTrue(CollectionUtil.removeAll(collection, "A"));
      assertEquals(5, collection.size());
      assertEquals("C", collection.get(0));
      assertEquals("D", collection.get(1));
      assertEquals("E", collection.get(2));
      assertEquals("F", collection.get(3));
      assertEquals("G", collection.get(4));      
      assertTrue(CollectionUtil.removeAll(collection, "C", "D"));
      assertEquals(3, collection.size());
      assertEquals("E", collection.get(0));
      assertEquals("F", collection.get(1));
      assertEquals("G", collection.get(2));
      assertTrue(CollectionUtil.removeAll(collection, new String[] {"F"}));
      assertEquals(2, collection.size());
      assertEquals("E", collection.get(0));
      assertEquals("G", collection.get(1));
      assertTrue(CollectionUtil.removeAll(collection, new String[] {"G", "E"}));
      assertEquals(0, collection.size());
   }

   /**
    * Test for {@link CollectionUtil#addAll(java.util.Collection, Object...)}
    */
   @Test
   public void testAddAll() {
      List<String> collection = new LinkedList<String>();
      CollectionUtil.addAll(null, "A");
      assertEquals(0, collection.size());
      CollectionUtil.addAll(collection, (String[])null);
      assertEquals(0, collection.size());
      CollectionUtil.addAll(collection, "A");
      assertEquals(1, collection.size());
      assertEquals("A", collection.get(0));
      CollectionUtil.addAll(collection, "B");
      assertEquals(2, collection.size());
      assertEquals("A", collection.get(0));
      assertEquals("B", collection.get(1));
      CollectionUtil.addAll(collection, "C", "D");
      assertEquals(4, collection.size());
      assertEquals("A", collection.get(0));
      assertEquals("B", collection.get(1));
      assertEquals("C", collection.get(2));
      assertEquals("D", collection.get(3));
      CollectionUtil.addAll(collection, new String[] {"E"});
      assertEquals(5, collection.size());
      assertEquals("A", collection.get(0));
      assertEquals("B", collection.get(1));
      assertEquals("C", collection.get(2));
      assertEquals("D", collection.get(3));
      assertEquals("E", collection.get(4));
      CollectionUtil.addAll(collection, new String[] {"F", "G"});
      assertEquals(7, collection.size());
      assertEquals("A", collection.get(0));
      assertEquals("B", collection.get(1));
      assertEquals("C", collection.get(2));
      assertEquals("D", collection.get(3));
      assertEquals("E", collection.get(4));
      assertEquals("F", collection.get(5));
      assertEquals("G", collection.get(6));
   }

   /**
    * Test for {@link CollectionUtil#toList(Object...)}
    */
   @Test
   public void testToList() {
      List<String> result = CollectionUtil.toList();
      assertEquals(0, result.size());
      result = CollectionUtil.toList((String[])null);
      assertEquals(0, result.size());
      result = CollectionUtil.toList("A");
      assertEquals(1, result.size());
      assertEquals("A", result.get(0));
      result = CollectionUtil.toList("A", "B");
      assertEquals(2, result.size());
      assertEquals("A", result.get(0));
      assertEquals("B", result.get(1));
      result = CollectionUtil.toList("A", "B", "C");
      assertEquals(3, result.size());
      assertEquals("A", result.get(0));
      assertEquals("B", result.get(1));
      assertEquals("C", result.get(2));
      result = CollectionUtil.toList(new String[] {"A"});
      assertEquals(1, result.size());
      assertEquals("A", result.get(0));
      result = CollectionUtil.toList(new String[] {"A", "B"});
      assertEquals(2, result.size());
      assertEquals("A", result.get(0));
      assertEquals("B", result.get(1));
      result = CollectionUtil.toList(new String[] {"A", "B", "C"});
      assertEquals(3, result.size());
      assertEquals("A", result.get(0));
      assertEquals("B", result.get(1));
      assertEquals("C", result.get(2));
   }
   
   /**
    * Test for {@link CollectionUtil#isEmpty(java.util.Collection)}
    */
   @Test
   public void testIsEmpty() {
      assertTrue(CollectionUtil.isEmpty(null));
      List<String> collection = new LinkedList<String>();
      assertTrue(CollectionUtil.isEmpty(collection));
      collection.add("A");
      assertFalse(CollectionUtil.isEmpty(collection));
      collection.add("B");
      assertFalse(CollectionUtil.isEmpty(collection));
      collection.add("C");
      assertFalse(CollectionUtil.isEmpty(collection));
   }
   
   /**
    * Test for {@link CollectionUtil#toString(java.util.Collection, String)}
    */
   @Test
   public void testToString_Collection_String() {
      assertEquals("", CollectionUtil.toString(null, " | "));
      List<String> collection = new LinkedList<String>();
      assertEquals("", CollectionUtil.toString(collection, " | "));
      collection.add("A");
      assertEquals("A", CollectionUtil.toString(collection, " | "));
      collection.add("B");
      assertEquals("A | B", CollectionUtil.toString(collection, " | "));
      collection.add("C");
      assertEquals("A | B | C", CollectionUtil.toString(collection, " | "));
      collection.add("D");
      assertEquals("A | B | C | D", CollectionUtil.toString(collection, " | "));
      assertEquals("ABCD", CollectionUtil.toString(collection, null));
   }
   /**
    * Test for {@link CollectionUtil#toString(java.util.Collection)}
    */
   @Test
   public void testToString_Collection() {
      assertEquals("", CollectionUtil.toString(null));
      List<String> collection = new LinkedList<String>();
      assertEquals("", CollectionUtil.toString(collection));
      collection.add("A");
      assertEquals("A", CollectionUtil.toString(collection));
      collection.add("B");
      assertEquals("A" + CollectionUtil.SEPARATOR + "B", CollectionUtil.toString(collection));
      collection.add("C");
      assertEquals("A" + CollectionUtil.SEPARATOR + "B" + CollectionUtil.SEPARATOR + "C", CollectionUtil.toString(collection));
      collection.add("D");
      assertEquals("A" + CollectionUtil.SEPARATOR + "B" + CollectionUtil.SEPARATOR + "C" + CollectionUtil.SEPARATOR + "D", CollectionUtil.toString(collection));
   }
}

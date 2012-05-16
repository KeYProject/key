package de.uka.ilkd.key.symbolic_execution.util;

import java.util.LinkedList;
import java.util.List;

import junit.framework.TestCase;

/**
 * Tests for {@link JavaUtil}.
 * @author Martin Hentschel
 */
public class TestJavaUtil extends TestCase {
   /**
    * Tests {@link JavaUtil#isEmpty(Object[])}
    */
   public void testIsEmpty() {
      assertTrue(JavaUtil.isEmpty(null));
      assertTrue(JavaUtil.isEmpty(new String[] {}));
      assertFalse(JavaUtil.isEmpty(new String[] {"A"}));
      assertFalse(JavaUtil.isEmpty(new String[] {null}));
      assertFalse(JavaUtil.isEmpty(new String[] {"A", "B"}));
   }
   
   /**
    * Tests {@link JavaUtil#isTrimmedEmpty(String)}
    */
   public void testIsTrimmedEmpty() {
      assertTrue(JavaUtil.isTrimmedEmpty(null));
      assertTrue(JavaUtil.isTrimmedEmpty(""));
      assertTrue(JavaUtil.isTrimmedEmpty(" "));
      assertFalse(JavaUtil.isTrimmedEmpty(" A "));
   }
   
   /**
    * Tests {@link JavaUtil#equals(Object, Object)}
    */
   public void testEquals() {
      assertTrue(JavaUtil.equals(null, null));
      assertFalse(JavaUtil.equals(null, "A"));
      assertFalse(JavaUtil.equals("A", null));
      assertTrue(JavaUtil.equals("A", "A"));
      assertFalse(JavaUtil.equals("A", "B"));
      assertFalse(JavaUtil.equals("B", "A"));
      assertTrue(JavaUtil.equals("B", "B"));
   }
   
   /**
    * Tests {@link JavaUtil#count(Iterable, IFilter)}.
    */
   public void testCount() {
      // Create model
      List<String> list = new LinkedList<String>();
      list.add("A");
      list.add("B");
      list.add("A");
      list.add("C");
      list.add("B");
      list.add("A");
      // Test counts
      assertEquals(0, JavaUtil.count(null, null));
      assertEquals(0, JavaUtil.count(list, null));
      assertEquals(0, JavaUtil.count(null, new IFilter<String>() {
         @Override
         public boolean select(String element) {
            return false;
         }
      }));
      assertEquals(3, JavaUtil.count(list, new IFilter<String>() {
         @Override
         public boolean select(String element) {
            return "A".equals(element);
         }
      }));
      assertEquals(2, JavaUtil.count(list, new IFilter<String>() {
         @Override
         public boolean select(String element) {
            return "B".equals(element);
         }
      }));
      assertEquals(1, JavaUtil.count(list, new IFilter<String>() {
         @Override
         public boolean select(String element) {
            return "C".equals(element);
         }
      }));
      assertEquals(0, JavaUtil.count(list, new IFilter<String>() {
         @Override
         public boolean select(String element) {
            return "D".equals(element);
         }
      }));
   }

   /**
    * Tests for {@link JavaUtil#search(Iterable, IFilter)}.
    */
   public void testSearch() {
       List<String> collection = new LinkedList<String>();
       collection.add("A");
       collection.add("B");
       collection.add("C");
       collection.add("D");
       assertEquals("A", JavaUtil.search(collection, new IFilter<String>() {
          @Override
          public boolean select(String element) {
             return "A".equals(element);
          }
       }));
       assertEquals("B", JavaUtil.search(collection, new IFilter<String>() {
          @Override
          public boolean select(String element) {
             return "B".equals(element);
          }
       }));
       assertEquals("C", JavaUtil.search(collection, new IFilter<String>() {
          @Override
          public boolean select(String element) {
             return "C".equals(element);
          }
       }));
       assertEquals("D", JavaUtil.search(collection, new IFilter<String>() {
          @Override
          public boolean select(String element) {
             return "D".equals(element);
          }
       }));
       assertNull(JavaUtil.search(collection, new IFilter<String>() {
          @Override
          public boolean select(String element) {
             return "E".equals(element);
          }
       }));
       assertNull(JavaUtil.search(collection, null));
       assertNull(JavaUtil.search(null, new IFilter<String>() {
          @Override
          public boolean select(String element) {
             return "E".equals(element);
          }
       }));
   }
}

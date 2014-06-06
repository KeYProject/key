// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.symbolic_execution.util;

import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import junit.framework.TestCase;

/**
 * Tests for {@link JavaUtil}.
 * @author Martin Hentschel
 */
public class TestJavaUtil extends TestCase {
   /**
    * Tests {@link JavaUtil#contains(Object[], Object)}
    */
   public void testContains() {
      String[] array = {"A", "B", "C"};
      assertFalse(JavaUtil.contains(array, null));
      assertFalse(JavaUtil.contains(null, "A"));
      assertTrue(JavaUtil.contains(array, "A"));
      assertTrue(JavaUtil.contains(array, "B"));
      assertTrue(JavaUtil.contains(array, "C"));
      assertFalse(JavaUtil.contains(array, "D"));
      String[] arrayWithNull = {"A", "B", null, "D"};
      assertTrue(JavaUtil.contains(arrayWithNull, null));
      assertFalse(JavaUtil.contains(null, "A"));
      assertTrue(JavaUtil.contains(arrayWithNull, "A"));
      assertTrue(JavaUtil.contains(arrayWithNull, "B"));
      assertFalse(JavaUtil.contains(arrayWithNull, "C"));
      assertTrue(JavaUtil.contains(arrayWithNull, "D"));
      assertFalse(JavaUtil.contains(arrayWithNull, "E"));
      String[] arrayWithDoubleElements = {"B", "A", "C", "B", "C"};
      assertFalse(JavaUtil.contains(arrayWithDoubleElements, null));
      assertFalse(JavaUtil.contains(null, "A"));
      assertTrue(JavaUtil.contains(arrayWithDoubleElements, "A"));
      assertTrue(JavaUtil.contains(arrayWithDoubleElements, "B"));
      assertTrue(JavaUtil.contains(arrayWithDoubleElements, "C"));
      assertFalse(JavaUtil.contains(arrayWithDoubleElements, "D"));
   }
   
   /**
    * Tests for {@link JavaUtil#toSortedString(java.util.Map)}
    */
   public void testSoSortedString() {
      // Test equality to toString() of maps
      Map<String, String> emptyMap = new HashMap<String, String>();
      Map<String, String> oneElementMap = new LinkedHashMap<String, String>();
      oneElementMap.put("A", "Value of A");
      Map<String, String> twoElementMap = new LinkedHashMap<String, String>();
      twoElementMap.put("B", "Value of B");
      twoElementMap.put("A", "Value of A");
      Map<String, String> threeElementMap = new LinkedHashMap<String, String>();
      threeElementMap.put("A", "Value of A");
      threeElementMap.put("B", "Value of B");
      threeElementMap.put("C", "Value of C");
      assertEquals(null, JavaUtil.toSortedString(null));
      assertEquals(emptyMap.toString(), JavaUtil.toSortedString(emptyMap));
      assertEquals(oneElementMap.toString(), JavaUtil.toSortedString(oneElementMap));
      assertEquals(threeElementMap.toString(), JavaUtil.toSortedString(threeElementMap));
      // Test sorting
      Map<String, String> fourElementMap = new LinkedHashMap<String, String>();
      fourElementMap.put("B", "Value of B");
      fourElementMap.put("A", "Value of A");
      fourElementMap.put("D", "Value of D");
      fourElementMap.put("C", "Value of C");
      assertEquals("{A=Value of A, B=Value of B, C=Value of C, D=Value of D}", JavaUtil.toSortedString(fourElementMap));
   }
   
   /**
    * Tests for {@link JavaUtil#searchAndRemove(Iterable, IFilter)}.
    */
   public void testSearchAndRemove() {
      List<String> collection = new LinkedList<String>();
      collection.add("A");
      collection.add("B");
      collection.add("C");
      collection.add("D");
       assertEquals("A", JavaUtil.searchAndRemove(collection, new IFilter<String>() {
          @Override
          public boolean select(String element) {
             return "A".equals(element);
          }
       }));
       assertNull("A", JavaUtil.searchAndRemove(collection, new IFilter<String>() {
          @Override
          public boolean select(String element) {
             return "A".equals(element);
          }
       }));
       assertEquals("B", JavaUtil.searchAndRemove(collection, new IFilter<String>() {
          @Override
          public boolean select(String element) {
             return "B".equals(element);
          }
       }));
       assertNull("B", JavaUtil.searchAndRemove(collection, new IFilter<String>() {
          @Override
          public boolean select(String element) {
             return "A".equals(element);
          }
       }));
       assertEquals("C", JavaUtil.searchAndRemove(collection, new IFilter<String>() {
          @Override
          public boolean select(String element) {
             return "C".equals(element);
          }
       }));
       assertNull("C", JavaUtil.searchAndRemove(collection, new IFilter<String>() {
          @Override
          public boolean select(String element) {
             return "A".equals(element);
          }
       }));
       assertEquals("D", JavaUtil.searchAndRemove(collection, new IFilter<String>() {
          @Override
          public boolean select(String element) {
             return "D".equals(element);
          }
       }));
       assertNull("D", JavaUtil.searchAndRemove(collection, new IFilter<String>() {
          @Override
          public boolean select(String element) {
             return "A".equals(element);
          }
       }));
       assertNull(JavaUtil.searchAndRemove(collection, new IFilter<String>() {
          @Override
          public boolean select(String element) {
             return "E".equals(element);
          }
       }));
       assertNull(JavaUtil.searchAndRemove(collection, null));
       assertNull(JavaUtil.searchAndRemove(null, new IFilter<String>() {
          @Override
          public boolean select(String element) {
             return "E".equals(element);
          }
       }));
   }
   
   /**
    * Test for {@link JavaUtil#addAll(java.util.Collection, Object...)}
    */
   public void testAddAll() {
      List<String> collection = new LinkedList<String>();
      JavaUtil.addAll(null, "A");
      assertEquals(0, collection.size());
      JavaUtil.addAll(collection, (String[])null);
      assertEquals(0, collection.size());
      JavaUtil.addAll(collection, "A");
      assertEquals(1, collection.size());
      assertEquals("A", collection.get(0));
      JavaUtil.addAll(collection, "B");
      assertEquals(2, collection.size());
      assertEquals("A", collection.get(0));
      assertEquals("B", collection.get(1));
      JavaUtil.addAll(collection, "C", "D");
      assertEquals(4, collection.size());
      assertEquals("A", collection.get(0));
      assertEquals("B", collection.get(1));
      assertEquals("C", collection.get(2));
      assertEquals("D", collection.get(3));
      JavaUtil.addAll(collection, new String[] {"E"});
      assertEquals(5, collection.size());
      assertEquals("A", collection.get(0));
      assertEquals("B", collection.get(1));
      assertEquals("C", collection.get(2));
      assertEquals("D", collection.get(3));
      assertEquals("E", collection.get(4));
      JavaUtil.addAll(collection, new String[] {"F", "G"});
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
    * Tests {@link JavaUtil#indexOf(Object[], Object)}
    */
   public void testIndexOf_array() {
      String[] array = {"A", "B", "C"};
      assertEquals(-1, JavaUtil.indexOf((Object[])null, null));
      assertEquals(-1, JavaUtil.indexOf(array, null));
      assertEquals(-1, JavaUtil.indexOf((String[])null, "A"));
      assertEquals(0, JavaUtil.indexOf(array, "A"));
      assertEquals(1, JavaUtil.indexOf(array, "B"));
      assertEquals(2, JavaUtil.indexOf(array, "C"));
      assertEquals(-1, JavaUtil.indexOf(array, "D"));
   }
   
   /**
    * Tests {@link JavaUtil#indexOf(java.util.Iterator, Object)}
    */
   public void testIndexOf_Iterator() {
      List<String> list = new LinkedList<String>();
      list.add("A");
      list.add("B");
      list.add("C");
      assertEquals(-1, JavaUtil.indexOf((Iterator<?>)null, null));
      assertEquals(-1, JavaUtil.indexOf(list.iterator(), null));
      assertEquals(-1, JavaUtil.indexOf((Iterator<String>)null, "A"));
      assertEquals(0, JavaUtil.indexOf(list.iterator(), "A"));
      assertEquals(1, JavaUtil.indexOf(list.iterator(), "B"));
      assertEquals(2, JavaUtil.indexOf(list.iterator(), "C"));
      assertEquals(-1, JavaUtil.indexOf(list.iterator(), "D"));
   }
   
   /**
    * Tests {@link JavaUtil#equalIgnoreWhiteSpace(String, String)}.
    */
   public void testEqualIgnoreWhiteSpace() {
      assertTrue(JavaUtil.equalIgnoreWhiteSpace(null, null));
      assertFalse(JavaUtil.equalIgnoreWhiteSpace("A", null));
      assertFalse(JavaUtil.equalIgnoreWhiteSpace("B", null));
      assertTrue(JavaUtil.equalIgnoreWhiteSpace("A", "A"));
      assertTrue(JavaUtil.equalIgnoreWhiteSpace("A B", "A B"));
      assertTrue(JavaUtil.equalIgnoreWhiteSpace("A B C", "A B C"));
      assertTrue(JavaUtil.equalIgnoreWhiteSpace("A    B    C", "A\nB\r\tC"));
      assertFalse(JavaUtil.equalIgnoreWhiteSpace("A B C", "A B C D"));
      assertFalse(JavaUtil.equalIgnoreWhiteSpace("A B C D", "A B C"));
      assertTrue(JavaUtil.equalIgnoreWhiteSpace("  A B C", "A B C\t\n"));
   }
   
   /**
    * Tests {@link JavaUtil#createLine(String, int)}
    */
   public void testCreateLine() {
      // Test line with one character
      assertEquals("", JavaUtil.createLine("#", -1));
      assertEquals("", JavaUtil.createLine("#", 0));
      assertEquals("-", JavaUtil.createLine("-", 1));
      assertEquals("AA", JavaUtil.createLine("A", 2));
      assertEquals("#####", JavaUtil.createLine("#", 5));
      // Test line with multiple characters
      assertEquals("ABABAB", JavaUtil.createLine("AB", 3));
      // Test null text
      assertEquals("nullnullnullnull", JavaUtil.createLine(null, 4));
   }
   
   /**
    * Tests {@link JavaUtil#encodeText(String)}
    */
   public void testEncodeText() {
      // Test null
      assertNull(JavaUtil.encodeText(null));
      // Test empty string
      assertEquals("", JavaUtil.encodeText(""));
      // Text XML tags
      assertEquals("&lt;hello&gt;world&lt;/hello&gt;", JavaUtil.encodeText("<hello>world</hello>"));
      // Test XML attributes
      assertEquals("&lt;hello a=&quot;A&quot; b=&apos;B&apos;&gt;world&lt;/hello&gt;", JavaUtil.encodeText("<hello a=\"A\" b='B'>world</hello>"));
      // Test XML entities
      assertEquals("&lt;hello a=&quot;A&quot; b=&apos;B&apos;&gt;&amp;lt;world&amp;gt;&lt;/hello&gt;", JavaUtil.encodeText("<hello a=\"A\" b='B'>&lt;world&gt;</hello>"));
   }
   
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
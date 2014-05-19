/*******************************************************************************
 * Copyright (c) 2014 Karlsruhe Institute of Technology, Germany
 *                    Technical University Darmstadt, Germany
 *                    Chalmers University of Technology, Sweden
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Technical University Darmstadt - initial API and implementation and/or initial documentation
 *******************************************************************************/

package org.key_project.util.test.testcase;

import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import junit.framework.TestCase;

import org.junit.Test;
import org.key_project.util.java.CollectionUtil;
import org.key_project.util.java.IFilter;
import org.key_project.util.java.IFilterWithException;

/**
 * Tests for {@link CollectionUtil}.
 * @author Martin Hentschel
 */
public class CollectionUtilTest extends TestCase {
   /**
    * Tests for {@link CollectionUtil#searchAndRemoveWithException(Iterable, org.key_project.util.java.IFilterWithException)}.
    */
   @Test
   public void testSearchAndRemoveWithException() throws Throwable {
       List<String> collection = CollectionUtil.toList("A", "B", "C", "D");
       try {
         CollectionUtil.searchAndRemoveWithException(collection, new IFilterWithException<String, Exception>() {
             @Override
             public boolean select(String element) throws Exception {
                throw new Exception("Exception in select.");
             }
          });
          fail("Exception expected");
       }
       catch (Exception e) {
          assertEquals("Exception in select.", e.getMessage());
       }
       assertEquals(collection, CollectionUtil.toList("A", "B", "C", "D"));
       assertEquals("A", CollectionUtil.searchAndRemoveWithException(collection, new IFilterWithException<String, Exception>() {
          @Override
          public boolean select(String element) {
             return "A".equals(element);
          }
       }));
       assertEquals(collection, CollectionUtil.toList("B", "C", "D"));
       assertNull("A", CollectionUtil.searchAndRemoveWithException(collection, new IFilterWithException<String, Exception>() {
          @Override
          public boolean select(String element) {
             return "A".equals(element);
          }
       }));
       assertEquals(collection, CollectionUtil.toList("B", "C", "D"));
       assertEquals("B", CollectionUtil.searchAndRemoveWithException(collection, new IFilterWithException<String, Exception>() {
          @Override
          public boolean select(String element) {
             return "B".equals(element);
          }
       }));
       assertEquals(collection, CollectionUtil.toList("C", "D"));
       assertNull("B", CollectionUtil.searchAndRemoveWithException(collection, new IFilterWithException<String, Exception>() {
          @Override
          public boolean select(String element) {
             return "A".equals(element);
          }
       }));
       assertEquals(collection, CollectionUtil.toList("C", "D"));
       assertEquals("C", CollectionUtil.searchAndRemoveWithException(collection, new IFilterWithException<String, Exception>() {
          @Override
          public boolean select(String element) {
             return "C".equals(element);
          }
       }));
       assertEquals(collection, CollectionUtil.toList("D"));
       assertNull("C", CollectionUtil.searchAndRemoveWithException(collection, new IFilterWithException<String, Exception>() {
          @Override
          public boolean select(String element) {
             return "A".equals(element);
          }
       }));
       assertEquals(collection, CollectionUtil.toList("D"));
       assertEquals("D", CollectionUtil.searchAndRemoveWithException(collection, new IFilterWithException<String, Exception>() {
          @Override
          public boolean select(String element) {
             return "D".equals(element);
          }
       }));
       assertEquals(collection, CollectionUtil.toList());
       assertNull("D", CollectionUtil.searchAndRemoveWithException(collection, new IFilterWithException<String, Exception>() {
          @Override
          public boolean select(String element) {
             return "A".equals(element);
          }
       }));
       assertEquals(collection, CollectionUtil.toList());
       assertNull(CollectionUtil.searchAndRemoveWithException(collection, new IFilterWithException<String, Exception>() {
          @Override
          public boolean select(String element) {
             return "E".equals(element);
          }
       }));
       assertEquals(collection, CollectionUtil.toList());
       assertNull(CollectionUtil.searchAndRemoveWithException(collection, null));
       assertNull(CollectionUtil.searchAndRemoveWithException(null, new IFilterWithException<String, Exception>() {
          @Override
          public boolean select(String element) {
             return "E".equals(element);
          }
       }));
       assertEquals(collection, CollectionUtil.toList());
   }
   
   /**
    * Tests for {@link CollectionUtil#searchAndRemove(Iterable, IFilter)}.
    */
   @Test
   public void testSearchAndRemove() {
       List<String> collection = CollectionUtil.toList("A", "B", "C", "D");
       assertEquals("A", CollectionUtil.searchAndRemove(collection, new IFilter<String>() {
          @Override
          public boolean select(String element) {
             return "A".equals(element);
          }
       }));
       assertEquals(collection, CollectionUtil.toList("B", "C", "D"));
       assertNull("A", CollectionUtil.searchAndRemove(collection, new IFilter<String>() {
          @Override
          public boolean select(String element) {
             return "A".equals(element);
          }
       }));
       assertEquals(collection, CollectionUtil.toList("B", "C", "D"));
       assertEquals("B", CollectionUtil.searchAndRemove(collection, new IFilter<String>() {
          @Override
          public boolean select(String element) {
             return "B".equals(element);
          }
       }));
       assertEquals(collection, CollectionUtil.toList("C", "D"));
       assertNull("B", CollectionUtil.searchAndRemove(collection, new IFilter<String>() {
          @Override
          public boolean select(String element) {
             return "A".equals(element);
          }
       }));
       assertEquals(collection, CollectionUtil.toList("C", "D"));
       assertEquals("C", CollectionUtil.searchAndRemove(collection, new IFilter<String>() {
          @Override
          public boolean select(String element) {
             return "C".equals(element);
          }
       }));
       assertEquals(collection, CollectionUtil.toList("D"));
       assertNull("C", CollectionUtil.searchAndRemove(collection, new IFilter<String>() {
          @Override
          public boolean select(String element) {
             return "A".equals(element);
          }
       }));
       assertEquals(collection, CollectionUtil.toList("D"));
       assertEquals("D", CollectionUtil.searchAndRemove(collection, new IFilter<String>() {
          @Override
          public boolean select(String element) {
             return "D".equals(element);
          }
       }));
       assertEquals(collection, CollectionUtil.toList());
       assertNull("D", CollectionUtil.searchAndRemove(collection, new IFilter<String>() {
          @Override
          public boolean select(String element) {
             return "A".equals(element);
          }
       }));
       assertEquals(collection, CollectionUtil.toList());
       assertNull(CollectionUtil.searchAndRemove(collection, new IFilter<String>() {
          @Override
          public boolean select(String element) {
             return "E".equals(element);
          }
       }));
       assertEquals(collection, CollectionUtil.toList());
       assertNull(CollectionUtil.searchAndRemove(collection, null));
       assertNull(CollectionUtil.searchAndRemove(null, new IFilter<String>() {
          @Override
          public boolean select(String element) {
             return "E".equals(element);
          }
       }));
       assertEquals(collection, CollectionUtil.toList());
   }
   
   /**
    * Tests {@link CollectionUtil#removeFirst(Iterable)}
    */
   @Test
   public void testRemoveFirst() {
      // Test null
      assertNull(CollectionUtil.removeFirst(null));
      // Test empty collection
      Set<String> set = Collections.emptySet();
      List<String> list = Collections.emptyList();
      assertNull(CollectionUtil.removeFirst(set));
      assertNull(CollectionUtil.removeFirst(list));
      assertTrue(set.isEmpty());
      assertTrue(list.isEmpty());
      // Test one element
      set = CollectionUtil.toSet("A");
      list = CollectionUtil.toList("A");
      assertEquals("A", CollectionUtil.removeFirst(set));
      assertEquals("A", CollectionUtil.removeFirst(list));
      assertTrue(set.isEmpty());
      assertTrue(list.isEmpty());
      // Test more elements
      set = CollectionUtil.toSet("A", "B");
      list = CollectionUtil.toList("A", "B");
      assertEquals("A", CollectionUtil.removeFirst(set));
      assertEquals("A", CollectionUtil.removeFirst(list));
      assertEquals("B", CollectionUtil.removeFirst(set));
      assertEquals("B", CollectionUtil.removeFirst(list));
      assertTrue(set.isEmpty());
      assertTrue(list.isEmpty());
   }
   
   /**
    * Tests {@link CollectionUtil#getFirst(Iterable)}
    */
   @Test
   public void testGetFirst() {
      // Test null
      assertNull(CollectionUtil.getFirst(null));
      // Test empty collection
      assertNull(CollectionUtil.getFirst(Collections.emptySet()));
      assertNull(CollectionUtil.getFirst(Collections.emptyList()));
      // Test one element
      assertEquals("A", CollectionUtil.getFirst(Collections.singleton("A")));
      assertEquals("A", CollectionUtil.getFirst(Collections.singletonList("A")));
      // Test more elements
      assertEquals("A", CollectionUtil.getFirst(CollectionUtil.toSet("A", "B")));
      assertEquals("A", CollectionUtil.getFirst(CollectionUtil.toList("A", "B")));
   }
   
   /**
    * Tests {@link CollectionUtil#containsSame(java.util.Set, java.util.Set)}.
    */
   @Test
   public void testContainsSame_List() {
      // Create model
      List<String> empty = new LinkedList<String>();
      List<String> one = Collections.singletonList("A");
      List<String> oneCopy = Collections.singletonList("A");
      List<String> oneDifferent = Collections.singletonList("B");
      List<String> two = CollectionUtil.toList("A", "B");
      List<String> twoCopy = CollectionUtil.toList("A", "B");
      List<String> twoDifferent = CollectionUtil.toList("C", "B");
      List<String> twoChangedOrder = CollectionUtil.toList("B", "A");
      List<String> three = CollectionUtil.toList("A", "B", "A");
      List<String> threeCopy = CollectionUtil.toList("A", "B", "A");
      List<String> threeDifferent = CollectionUtil.toList("A", "B", "B");
      List<String> threeChangedOrder = CollectionUtil.toList("A", "A", "B");
      List<String> four = CollectionUtil.toList("A", "B", null, "A");
      List<String> fourCopy = CollectionUtil.toList("A", "B", null, "A");
      List<String> fourDifferent = CollectionUtil.toList("A", null, null, "B");
      List<String> fourChangedOrder = CollectionUtil.toList(null, "A", "A", "B");
      // Test handlig of null
      assertTrue(CollectionUtil.containsSame(null, null));
      assertTrue(CollectionUtil.containsSame(empty, null));
      assertTrue(CollectionUtil.containsSame(null, empty));
      assertFalse(CollectionUtil.containsSame(null, one));
      assertFalse(CollectionUtil.containsSame(one, null));
      // Test one elements
      assertTrue(CollectionUtil.containsSame(one, one));
      assertTrue(CollectionUtil.containsSame(one, oneCopy));
      assertFalse(CollectionUtil.containsSame(one, oneDifferent));
      assertFalse(CollectionUtil.containsSame(one, two));
      assertFalse(CollectionUtil.containsSame(one, twoCopy));
      assertFalse(CollectionUtil.containsSame(one, twoDifferent));
      assertFalse(CollectionUtil.containsSame(one, twoChangedOrder));
      assertFalse(CollectionUtil.containsSame(one, three));
      assertFalse(CollectionUtil.containsSame(one, threeCopy));
      assertFalse(CollectionUtil.containsSame(one, threeDifferent));
      assertFalse(CollectionUtil.containsSame(one, threeChangedOrder));
      assertFalse(CollectionUtil.containsSame(one, four));
      assertFalse(CollectionUtil.containsSame(one, fourCopy));
      assertFalse(CollectionUtil.containsSame(one, fourDifferent));
      assertFalse(CollectionUtil.containsSame(one, fourChangedOrder));
      // Test two elements
      assertFalse(CollectionUtil.containsSame(two, one));
      assertFalse(CollectionUtil.containsSame(two, oneCopy));
      assertFalse(CollectionUtil.containsSame(two, oneDifferent));
      assertTrue(CollectionUtil.containsSame(two, two));
      assertTrue(CollectionUtil.containsSame(two, twoCopy));
      assertFalse(CollectionUtil.containsSame(two, twoDifferent));
      assertTrue(CollectionUtil.containsSame(two, twoChangedOrder));
      assertFalse(CollectionUtil.containsSame(two, three));
      assertFalse(CollectionUtil.containsSame(two, threeCopy));
      assertFalse(CollectionUtil.containsSame(two, threeDifferent));
      assertFalse(CollectionUtil.containsSame(two, threeChangedOrder));
      assertFalse(CollectionUtil.containsSame(two, four));
      assertFalse(CollectionUtil.containsSame(two, fourCopy));
      assertFalse(CollectionUtil.containsSame(two, fourDifferent));
      assertFalse(CollectionUtil.containsSame(two, fourChangedOrder));
      // Test three elements
      assertFalse(CollectionUtil.containsSame(three, one));
      assertFalse(CollectionUtil.containsSame(three, oneCopy));
      assertFalse(CollectionUtil.containsSame(three, oneDifferent));
      assertFalse(CollectionUtil.containsSame(three, two));
      assertFalse(CollectionUtil.containsSame(three, twoCopy));
      assertFalse(CollectionUtil.containsSame(three, twoDifferent));
      assertFalse(CollectionUtil.containsSame(three, twoChangedOrder));
      assertTrue(CollectionUtil.containsSame(three, three));
      assertTrue(CollectionUtil.containsSame(three, threeCopy));
      assertFalse(CollectionUtil.containsSame(three, threeDifferent));
      assertTrue(CollectionUtil.containsSame(three, threeChangedOrder));
      assertFalse(CollectionUtil.containsSame(three, four));
      assertFalse(CollectionUtil.containsSame(three, fourCopy));
      assertFalse(CollectionUtil.containsSame(three, fourDifferent));
      assertFalse(CollectionUtil.containsSame(three, fourChangedOrder));
      // Test four elements
      assertFalse(CollectionUtil.containsSame(four, one));
      assertFalse(CollectionUtil.containsSame(four, oneCopy));
      assertFalse(CollectionUtil.containsSame(four, oneDifferent));
      assertFalse(CollectionUtil.containsSame(four, two));
      assertFalse(CollectionUtil.containsSame(four, twoCopy));
      assertFalse(CollectionUtil.containsSame(four, twoDifferent));
      assertFalse(CollectionUtil.containsSame(four, twoChangedOrder));
      assertFalse(CollectionUtil.containsSame(four, three));
      assertFalse(CollectionUtil.containsSame(four, threeCopy));
      assertFalse(CollectionUtil.containsSame(four, threeDifferent));
      assertFalse(CollectionUtil.containsSame(four, threeChangedOrder));
      assertTrue(CollectionUtil.containsSame(four, four));
      assertTrue(CollectionUtil.containsSame(four, fourCopy));
      assertFalse(CollectionUtil.containsSame(four, fourDifferent));
      assertTrue(CollectionUtil.containsSame(four, fourChangedOrder));
   }
   
   /**
    * Tests {@link CollectionUtil#containsSame(java.util.Set, java.util.Set)}.
    */
   @Test
   public void testContainsSame_Set() {
      // Create model
      Set<String> empty = new HashSet<String>();
      Set<String> one = Collections.singleton("A");
      Set<String> oneCopy = Collections.singleton("A");
      Set<String> oneDifferent = Collections.singleton("B");
      Set<String> two = CollectionUtil.toSet("A", "B");
      Set<String> twoCopy = CollectionUtil.toSet("A", "B");
      Set<String> twoDifferent = CollectionUtil.toSet("C", "B");
      Set<String> twoChangedOrder = CollectionUtil.toSet("B", "A");
      // Test handlig of null
      assertTrue(CollectionUtil.containsSame(null, null));
      assertTrue(CollectionUtil.containsSame(empty, null));
      assertTrue(CollectionUtil.containsSame(null, empty));
      assertFalse(CollectionUtil.containsSame(null, one));
      assertFalse(CollectionUtil.containsSame(one, null));
      // Test one elements
      assertTrue(CollectionUtil.containsSame(one, one));
      assertTrue(CollectionUtil.containsSame(one, oneCopy));
      assertFalse(CollectionUtil.containsSame(one, oneDifferent));
      assertFalse(CollectionUtil.containsSame(one, two));
      assertFalse(CollectionUtil.containsSame(one, twoCopy));
      assertFalse(CollectionUtil.containsSame(one, twoDifferent));
      assertFalse(CollectionUtil.containsSame(one, twoChangedOrder));
      // Test two elements
      assertFalse(CollectionUtil.containsSame(two, one));
      assertFalse(CollectionUtil.containsSame(two, oneCopy));
      assertFalse(CollectionUtil.containsSame(two, oneDifferent));
      assertTrue(CollectionUtil.containsSame(two, two));
      assertTrue(CollectionUtil.containsSame(two, twoCopy));
      assertFalse(CollectionUtil.containsSame(two, twoDifferent));
      assertTrue(CollectionUtil.containsSame(two, twoChangedOrder));
   }
   
   /**
    * Tests {@link CollectionUtil#count(Iterable, IFilter)}.
    */
   @Test
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
      assertEquals(0, CollectionUtil.count(null, null));
      assertEquals(0, CollectionUtil.count(list, null));
      assertEquals(0, CollectionUtil.count(null, new IFilter<String>() {
         @Override
         public boolean select(String element) {
            return false;
         }
      }));
      assertEquals(3, CollectionUtil.count(list, new IFilter<String>() {
         @Override
         public boolean select(String element) {
            return "A".equals(element);
         }
      }));
      assertEquals(2, CollectionUtil.count(list, new IFilter<String>() {
         @Override
         public boolean select(String element) {
            return "B".equals(element);
         }
      }));
      assertEquals(1, CollectionUtil.count(list, new IFilter<String>() {
         @Override
         public boolean select(String element) {
            return "C".equals(element);
         }
      }));
      assertEquals(0, CollectionUtil.count(list, new IFilter<String>() {
         @Override
         public boolean select(String element) {
            return "D".equals(element);
         }
      }));
   }
   
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
    * Test for {@link CollectionUtil#addAll(Collection, Iterable)}
    */
   @Test
   public void testAddAll_Iterable() {
      List<String> collection = new LinkedList<String>();
      CollectionUtil.addAll(null, CollectionUtil.toList("A"));
      assertEquals(0, collection.size());
      CollectionUtil.addAll(collection, (Iterable<String>)null);
      assertEquals(0, collection.size());
      CollectionUtil.addAll(collection, CollectionUtil.toList("A"));
      assertEquals(1, collection.size());
      assertEquals("A", collection.get(0));
      CollectionUtil.addAll(collection, CollectionUtil.toList("B"));
      assertEquals(2, collection.size());
      assertEquals("A", collection.get(0));
      assertEquals("B", collection.get(1));
      CollectionUtil.addAll(collection, CollectionUtil.toList("C", "D"));
      assertEquals(4, collection.size());
      assertEquals("A", collection.get(0));
      assertEquals("B", collection.get(1));
      assertEquals("C", collection.get(2));
      assertEquals("D", collection.get(3));
      CollectionUtil.addAll(collection, CollectionUtil.toList("E"));
      assertEquals(5, collection.size());
      assertEquals("A", collection.get(0));
      assertEquals("B", collection.get(1));
      assertEquals("C", collection.get(2));
      assertEquals("D", collection.get(3));
      assertEquals("E", collection.get(4));
      CollectionUtil.addAll(collection, CollectionUtil.toList("F", "G"));
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
    * Test for {@link CollectionUtil#addAll(java.util.Collection, Object...)}
    */
   @Test
   public void testAddAll_Array() {
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
    * Test for {@link CollectionUtil#toSet(Object...)}
    */
   @Test
   public void testToSet() {
      Set<String> result = CollectionUtil.toSet();
      assertEquals(0, result.size());
      result = CollectionUtil.toSet((String[])null);
      assertEquals(0, result.size());
      result = CollectionUtil.toSet("A");
      assertCollectionItems(result, "A");
      result = CollectionUtil.toSet("A", "B");
      assertCollectionItems(result, "A", "B");
      result = CollectionUtil.toSet("A", "B", "C");
      assertCollectionItems(result, "A", "B", "C");
      result = CollectionUtil.toSet(new String[] {"A"});
      assertCollectionItems(result, "A");
      result = CollectionUtil.toSet(new String[] {"A", "B"});
      assertCollectionItems(result, "A", "B");
      result = CollectionUtil.toSet(new String[] {"A", "B", "C"});
      assertCollectionItems(result, "A", "B", "C");
   }
   
   /**
    * Makes sure that the collection contains the given items.
    * @param collection The {@link Collections} to test.
    * @param expectedItems The expected items.
    */
   protected <T> void assertCollectionItems(Collection<T> collection, T... expectedItems) {
      assertNotNull(collection);
      assertEquals(collection.size(), expectedItems.length);
      Iterator<T> iter = collection.iterator();
      int i = 0;
      while (iter.hasNext()) {
         assertEquals(expectedItems[i], iter.next());
         i++;
      }
      assertEquals(expectedItems.length, i);
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
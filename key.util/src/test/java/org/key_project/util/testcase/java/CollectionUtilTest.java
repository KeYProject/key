/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.util.testcase.java;

import java.util.*;
import java.util.function.Predicate;

import org.key_project.util.java.CollectionUtil;
import org.key_project.util.java.IFilterWithException;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Tests for {@link CollectionUtil}.
 *
 * @author Martin Hentschel
 */
public class CollectionUtilTest {
    /**
     * Tests for {@link CollectionUtil#searchAll(Iterable, Predicate)}.
     */
    @Test
    public void testSearchAll() {
        // Test single existing values
        List<String> collection = Arrays.asList("A", "B", "C", "D");
        List<String> found = CollectionUtil.searchAll(collection, "A"::equals);
        assertList(found, "A");
        found = CollectionUtil.searchAll(collection, "B"::equals);
        assertList(found, "B");
        found = CollectionUtil.searchAll(collection, "C"::equals);
        assertList(found, "C");
        found = CollectionUtil.searchAll(collection, "D"::equals);
        assertList(found, "D");
        // Test single not existing value
        found = CollectionUtil.searchAll(collection, "E"::equals);
        assertList(found);
        // Test null
        found = CollectionUtil.searchAll(collection, null);
        assertList(found);
        found = CollectionUtil.searchAll(null, "E"::equals);
        assertList(found);
        // Test multible values
        found = CollectionUtil.searchAll(collection,
            element -> "A".equals(element) || "C".equals(element));
        assertList(found, "A", "C");
        found = CollectionUtil.searchAll(collection, element -> true);
        assertList(found, collection.toArray(new String[0]));
    }

    /**
     * Tests {@link CollectionUtil#binaryInsert(List, Object, java.util.Comparator)}.
     */
    @Test
    public void testBinaryInsert() {
        Comparator<String> comparator = String::compareTo;
        List<String> list = new LinkedList<>();
        CollectionUtil.binaryInsert(list, "C", comparator);
        assertList(list, "C");
        CollectionUtil.binaryInsert(list, "A", comparator);
        assertList(list, "A", "C");
        CollectionUtil.binaryInsert(list, "F", comparator);
        assertList(list, "A", "C", "F");
        CollectionUtil.binaryInsert(list, "B", comparator);
        assertList(list, "A", "B", "C", "F");
        CollectionUtil.binaryInsert(list, "D", comparator);
        assertList(list, "A", "B", "C", "D", "F");
        CollectionUtil.binaryInsert(list, "E", comparator);
        assertList(list, "A", "B", "C", "D", "E", "F");
        CollectionUtil.binaryInsert(list, "D", comparator);
        assertList(list, "A", "B", "C", "D", "D", "E", "F");
        CollectionUtil.binaryInsert(list, "A", comparator);
        assertList(list, "A", "A", "B", "C", "D", "D", "E", "F");
        CollectionUtil.binaryInsert(list, "F", comparator);
        assertList(list, "A", "A", "B", "C", "D", "D", "E", "F", "F");
    }

    /**
     * Ensures that the given {@link List} contains the expected elements.
     *
     * @param actual The actual {@link List}.
     * @param expected The expected elements.
     */
    protected static <T> void assertList(List<T> actual, String... expected) {
        assertEquals(expected.length, actual.size());
        int i = 0;
        for (T actualElement : actual) {
            assertEquals(expected[i], actualElement);
            i++;
        }
    }

    /**
     * Tests {@link CollectionUtil#indexOf(java.util.Iterator, Object)}
     */
    @Test
    public void testIndexOf_Iterator() {
        List<String> list = new LinkedList<>();
        list.add("A");
        list.add("B");
        list.add("C");
        assertEquals(-1, CollectionUtil.indexOf((Iterator<?>) null, null));
        assertEquals(-1, CollectionUtil.indexOf(list.iterator(), null));
        assertEquals(-1, CollectionUtil.indexOf(null, "A"));
        assertEquals(0, CollectionUtil.indexOf(list.iterator(), "A"));
        assertEquals(1, CollectionUtil.indexOf(list.iterator(), "B"));
        assertEquals(2, CollectionUtil.indexOf(list.iterator(), "C"));
        assertEquals(-1, CollectionUtil.indexOf(list.iterator(), "D"));
    }

    /**
     * Tests for
     * {@link CollectionUtil#searchAndRemoveWithException(Iterable, org.key_project.util.java.IFilterWithException)}.
     */
    @Test
    public void testSearchAndRemoveWithException() throws Throwable {
        List<String> collection = new ArrayList<>(Arrays.asList("A", "B", "C", "D"));
        try {
            CollectionUtil.searchAndRemoveWithException(collection, element -> {
                throw new Exception("Exception in select.");
            });
            fail("Exception expected");
        } catch (Exception e) {
            assertEquals("Exception in select.", e.getMessage());
        }
        assertEquals(collection, Arrays.asList("A", "B", "C", "D"));
        assertEquals("A", CollectionUtil.searchAndRemoveWithException(collection,
            (IFilterWithException<String, Exception>) "A"::equals));
        assertEquals(collection, Arrays.asList("B", "C", "D"));
        assertNull(CollectionUtil.searchAndRemoveWithException(collection,
            (IFilterWithException<String, Exception>) "A"::equals));
        assertEquals(collection, Arrays.asList("B", "C", "D"));
        assertEquals("B", CollectionUtil.searchAndRemoveWithException(collection,
            (IFilterWithException<String, Exception>) "B"::equals));
        assertEquals(collection, Arrays.asList("C", "D"));
        assertNull(CollectionUtil.searchAndRemoveWithException(collection,
            (IFilterWithException<String, Exception>) "A"::equals));
        assertEquals(collection, Arrays.asList("C", "D"));
        assertEquals("C", CollectionUtil.searchAndRemoveWithException(collection,
            (IFilterWithException<String, Exception>) "C"::equals));
        assertEquals(collection, List.of("D"));
        assertNull(CollectionUtil.searchAndRemoveWithException(collection,
            (IFilterWithException<String, Exception>) "A"::equals));
        assertEquals(collection, List.of("D"));
        assertEquals("D", CollectionUtil.searchAndRemoveWithException(collection,
            (IFilterWithException<String, Exception>) "D"::equals));
        assertEquals(collection, List.of());
        assertNull(CollectionUtil.searchAndRemoveWithException(collection,
            (IFilterWithException<String, Exception>) "A"::equals));
        assertEquals(collection, List.of());
        assertNull(CollectionUtil.searchAndRemoveWithException(collection,
            (IFilterWithException<String, Exception>) "E"::equals));
        assertEquals(collection, List.of());
        assertNull(CollectionUtil.searchAndRemoveWithException(collection, null));
        assertNull(CollectionUtil.searchAndRemoveWithException(null,
            (IFilterWithException<String, Exception>) "E"::equals));
        assertEquals(collection, List.of());
    }

    /**
     * Tests for {@link CollectionUtil#searchAndRemove(Iterable, Predicate)}.
     */
    @Test
    public void testSearchAndRemove() {
        List<String> collection = new ArrayList<>(List.of("A", "B", "C", "D"));
        assertEquals("A", CollectionUtil.searchAndRemove(collection, "A"::equals));
        assertEquals(collection, List.of("B", "C", "D"));
        assertNull(CollectionUtil.searchAndRemove(collection, "A"::equals));
        assertEquals(collection, List.of("B", "C", "D"));
        assertEquals("B", CollectionUtil.searchAndRemove(collection, "B"::equals));
        assertEquals(collection, List.of("C", "D"));
        assertNull(CollectionUtil.searchAndRemove(collection, "A"::equals));
        assertEquals(collection, List.of("C", "D"));
        assertEquals("C", CollectionUtil.searchAndRemove(collection, "C"::equals));
        assertEquals(collection, List.of("D"));
        assertNull(CollectionUtil.searchAndRemove(collection, "A"::equals));
        assertEquals(collection, List.of("D"));
        assertEquals("D", CollectionUtil.searchAndRemove(collection, "D"::equals));
        assertEquals(collection, List.of());
        assertNull(CollectionUtil.searchAndRemove(collection, "A"::equals));
        assertEquals(collection, List.of());
        assertNull(CollectionUtil.searchAndRemove(collection, "E"::equals));
        assertEquals(collection, List.of());
        assertNull(CollectionUtil.searchAndRemove(collection, null));
        assertNull(CollectionUtil.searchAndRemove(null, "E"::equals));
        assertEquals(collection, List.of());
    }

    /**
     * Tests {@link CollectionUtil#removeFirst(Iterable)}
     */
    @Test
    public void testRemoveFirst() {
        // Test null
        assertNull(CollectionUtil.removeFirst(null));
        // Test empty collection
        Set<String> set = new HashSet<>();
        List<String> list = new ArrayList<>();
        assertNull(CollectionUtil.removeFirst(set));
        assertNull(CollectionUtil.removeFirst(list));
        assertTrue(set.isEmpty());
        assertTrue(list.isEmpty());
        // Test one element
        set = new HashSet<>(Set.of("A"));
        list = new ArrayList<>(List.of("A"));
        assertEquals("A", CollectionUtil.removeFirst(set));
        assertEquals("A", CollectionUtil.removeFirst(list));
        assertTrue(set.isEmpty());
        assertTrue(list.isEmpty());
        // Test more elements
        set = new HashSet<>(Set.of("A", "B"));
        list = new ArrayList<>(Arrays.asList("A", "B"));
        assertEquals("A", CollectionUtil.removeFirst(set));
        assertEquals("A", CollectionUtil.removeFirst(list));
        assertEquals("B", CollectionUtil.removeFirst(set));
        assertEquals("B", CollectionUtil.removeFirst(list));
        assertTrue(set.isEmpty());
        assertTrue(list.isEmpty());
    }

    @Test
    public void testContainsSame_List() {
        // Create model
        List<String> empty = new LinkedList<>();
        List<String> one = Collections.singletonList("A");
        List<String> oneCopy = Collections.singletonList("A");
        List<String> oneDifferent = Collections.singletonList("B");
        List<String> two = Arrays.asList("A", "B");
        List<String> twoCopy = Arrays.asList("A", "B");
        List<String> twoDifferent = Arrays.asList("C", "B");
        List<String> twoChangedOrder = Arrays.asList("B", "A");
        List<String> three = Arrays.asList("A", "B", "A");
        List<String> threeCopy = Arrays.asList("A", "B", "A");
        List<String> threeDifferent = Arrays.asList("A", "B", "B");
        List<String> threeChangedOrder = Arrays.asList("A", "A", "B");
        List<String> four = Arrays.asList("A", "B", null, "A");
        List<String> fourCopy = Arrays.asList("A", "B", null, "A");
        List<String> fourDifferent = Arrays.asList("A", null, null, "B");
        List<String> fourChangedOrder = Arrays.asList(null, "A", "A", "B");
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

    @Test
    public void testContainsSame_Set() {
        // Create model
        Set<String> empty = new HashSet<>();
        Set<String> one = Collections.singleton("A");
        Set<String> oneCopy = Collections.singleton("A");
        Set<String> oneDifferent = Collections.singleton("B");
        Set<String> two = Set.of("A", "B");
        Set<String> twoCopy = Set.of("A", "B");
        Set<String> twoDifferent = Set.of("C", "B");
        Set<String> twoChangedOrder = Set.of("B", "A");
        // Test handlig of null
        assertTrue(CollectionUtil.containsSame(null, null));
        assertTrue(CollectionUtil.containsSame(empty, null));
        assertTrue(CollectionUtil.containsSame(null, empty));
        assertFalse(CollectionUtil.containsSame(null, one));
        assertFalse(CollectionUtil.containsSame(one, null));
        // Test one element
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
     * Tests {@link CollectionUtil#count(Iterable, Predicate)}.
     */
    @Test
    public void testCount() {
        // Create model
        List<String> list = new LinkedList<>();
        list.add("A");
        list.add("B");
        list.add("A");
        list.add("C");
        list.add("B");
        list.add("A");
        // Test counts
        assertEquals(0, CollectionUtil.count(null, null));
        assertEquals(0, CollectionUtil.count(list, null));
        assertEquals(0, CollectionUtil.count(null, element -> false));
        assertEquals(3, CollectionUtil.count(list, "A"::equals));
        assertEquals(2, CollectionUtil.count(list, "B"::equals));
        assertEquals(1, CollectionUtil.count(list, "C"::equals));
        assertEquals(0, CollectionUtil.count(list, "D"::equals));
    }

    /**
     * Tests {@link CollectionUtil#contains(Iterable, Object)}
     */
    @Test
    public void testContains() {
        // Create model
        List<String> list = new LinkedList<>();
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
     * Tests for {@link CollectionUtil#search(Iterable, Predicate)}.
     */
    @Test
    public void testSearch() {
        List<String> collection = Arrays.asList("A", "B", "C", "D");
        assertEquals("A", CollectionUtil.search(collection, "A"::equals));
        assertEquals("B", CollectionUtil.search(collection, "B"::equals));
        assertEquals("C", CollectionUtil.search(collection, "C"::equals));
        assertEquals("D", CollectionUtil.search(collection, "D"::equals));
        assertNull(CollectionUtil.search(collection, "E"::equals));
        assertNull(CollectionUtil.search(collection, null));
        assertNull(CollectionUtil.search(null, "E"::equals));
    }

    /**
     * Test for {@link CollectionUtil#removeComplete(java.util.Collection, Object)}
     */
    @Test
    public void testRemoveComplete() {
        List<String> collection =
            new ArrayList<>(Arrays.asList("A", "B", "C", "A", "A", "B", "A", "D"));
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
     * Test for {@link CollectionUtil#addAll(Collection, Iterable)}
     */
    @Test
    public void testAddAll_Iterable() {
        List<String> collection = new LinkedList<>();
        CollectionUtil.addAll(null, List.of("A"));
        assertEquals(0, collection.size());
        CollectionUtil.addAll(collection, null);
        assertEquals(0, collection.size());
        CollectionUtil.addAll(collection, List.of("A"));
        assertEquals(1, collection.size());
        assertEquals("A", collection.get(0));
        CollectionUtil.addAll(collection, List.of("B"));
        assertEquals(2, collection.size());
        assertEquals("A", collection.get(0));
        assertEquals("B", collection.get(1));
        CollectionUtil.addAll(collection, Arrays.asList("C", "D"));
        assertEquals(4, collection.size());
        assertEquals("A", collection.get(0));
        assertEquals("B", collection.get(1));
        assertEquals("C", collection.get(2));
        assertEquals("D", collection.get(3));
        CollectionUtil.addAll(collection, List.of("E"));
        assertEquals(5, collection.size());
        assertEquals("A", collection.get(0));
        assertEquals("B", collection.get(1));
        assertEquals("C", collection.get(2));
        assertEquals("D", collection.get(3));
        assertEquals("E", collection.get(4));
        CollectionUtil.addAll(collection, Arrays.asList("F", "G"));
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
     * Test for {@link CollectionUtil#isEmpty(java.util.Collection)}
     */
    @Test
    public void testIsEmpty_Collection() {
        assertTrue(CollectionUtil.isEmpty((Collection<?>) null));
        List<String> collection = new LinkedList<>();
        assertTrue(CollectionUtil.isEmpty(collection));
        collection.add("A");
        assertFalse(CollectionUtil.isEmpty(collection));
        collection.add("B");
        assertFalse(CollectionUtil.isEmpty(collection));
        collection.add("C");
        assertFalse(CollectionUtil.isEmpty(collection));
    }

    /**
     * Test for {@link CollectionUtil#isEmpty(java.util.Map)}
     */
    @Test
    public void testIsEmpty_Map() {
        assertTrue(CollectionUtil.isEmpty((Map<?, ?>) null));
        Map<String, String> map = new HashMap<>();
        assertTrue(CollectionUtil.isEmpty(map));
        map.put("A", "A");
        assertFalse(CollectionUtil.isEmpty(map));
        map.put("B", "B");
        assertFalse(CollectionUtil.isEmpty(map));
        map.put("C", "C");
        assertFalse(CollectionUtil.isEmpty(map));
    }

    /**
     * Test for {@link CollectionUtil#toString(java.util.Collection, String)}
     */
    @Test
    public void testToString_Collection_String() {
        assertEquals("", CollectionUtil.toString(null, " | "));
        List<String> collection = new LinkedList<>();
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
        List<String> collection = new LinkedList<>();
        assertEquals("", CollectionUtil.toString(collection));
        collection.add("A");
        assertEquals("A", CollectionUtil.toString(collection));
        collection.add("B");
        assertEquals("A" + CollectionUtil.SEPARATOR + "B", CollectionUtil.toString(collection));
        collection.add("C");
        assertEquals("A" + CollectionUtil.SEPARATOR + "B" + CollectionUtil.SEPARATOR + "C",
            CollectionUtil.toString(collection));
        collection.add("D");
        assertEquals("A" + CollectionUtil.SEPARATOR + "B" + CollectionUtil.SEPARATOR + "C"
            + CollectionUtil.SEPARATOR + "D", CollectionUtil.toString(collection));
    }
}

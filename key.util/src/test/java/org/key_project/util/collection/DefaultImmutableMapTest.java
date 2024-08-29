/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.util.collection;

import java.util.Iterator;

import org.checkerframework.checker.nullness.qual.MonotonicNonNull;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

public class DefaultImmutableMapTest {

    private @MonotonicNonNull ImmutableMap<String, Integer> map;

    @BeforeEach
    public void setUp() {
        map = DefaultImmutableMap.nilMap();
    }

    @Test
    public void testPutAndGet() {
        assertNotNull(map);
        map = map.put("one", 1);
        Integer one = map.get("one");
        assertNotNull(one);
        assertEquals(1, one);
    }

    @Test
    public void testSize() {
        assertNotNull(map);
        assertEquals(0, map.size());
        map = map.put("one", 1);
        assertEquals(1, map.size());
        map = map.put("two", 1);
        assertEquals(2, map.size());
        map = map.put("two", 2);
        assertEquals(2, map.size());
        map = map.put("one", 3);
        assertEquals(2, map.size());
    }

    @Test
    public void testIsEmpty() {
        assertNotNull(map);
        assertTrue(map.isEmpty());
        map = map.put("one", 1);
        assertFalse(map.isEmpty());
    }

    @Test
    public void testContainsKey() {
        assertNotNull(map);
        map = map.put("one", 1);
        assertTrue(map.containsKey("one"));
        assertFalse(map.containsKey("two"));
    }

    @Test
    public void testContainsValue() {
        assertNotNull(map);
        map = map.put("one", 1);
        assertTrue(map.containsValue(1));
        assertFalse(map.containsValue(2));
    }

    @Test
    public void testRemove() {
        assertNotNull(map);
        map = map.put("one", 1);
        map = map.remove("one");
        assertFalse(map.containsKey("one"));
        assertEquals(0, map.size());

        map = DefaultImmutableMap.nilMap();
        map = map.put("one", 1);
        map = map.remove("two");
        assertTrue(map.containsKey("one"));
        assertEquals(1, map.size());
    }

    @Test
    public void testRemoveAll() {
        assertNotNull(map);
        map = map.put("one", 1);
        map = map.put("two", 1);
        map = map.removeAll(1);
        assertFalse(map.containsValue(1));
        assertEquals(0, map.size());
    }

    @Test
    public void testKeyIterator() {
        assertNotNull(map);
        map = map.put("one", 1);
        map = map.put("two", 2);
        Iterator<String> iterator = map.keyIterator();
        assertTrue(iterator.hasNext());
        assertEquals("two", iterator.next());
        assertTrue(iterator.hasNext());
        assertEquals("one", iterator.next());
        assertFalse(iterator.hasNext());
    }

    @Test
    public void testValueIterator() {
        assertNotNull(map);
        map = map.put("one", 1);
        map = map.put("two", 2);
        Iterator<Integer> iterator = map.valueIterator();
        assertTrue(iterator.hasNext());
        assertEquals(2, iterator.next());
        assertTrue(iterator.hasNext());
        assertEquals(1, iterator.next());
        assertFalse(iterator.hasNext());
    }

    @Test
    public void testIterator() {
        assertNotNull(map);
        map = map.put("one", 1);
        map = map.put("two", 2);
        Iterator<ImmutableMapEntry<String, Integer>> iterator = map.iterator();
        assertTrue(iterator.hasNext());
        ImmutableMapEntry<String, Integer> entry = iterator.next();
        assertEquals("two", entry.key());
        assertEquals(2, entry.value());
        assertTrue(iterator.hasNext());
        entry = iterator.next();
        assertEquals("one", entry.key());
        assertEquals(1, entry.value());
        assertFalse(iterator.hasNext());
    }
}

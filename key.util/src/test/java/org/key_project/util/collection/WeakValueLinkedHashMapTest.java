/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.util.collection;

import org.jspecify.annotations.Nullable;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

class WeakValueLinkedHashMapTest {

    // make reasonably sure that gc has been run and collected unreachable objects
    private void encourageGC(int nr) {
        for (int i = 0; i < nr; i++) {
            System.gc();
        }
    }

    @Test
    void putAndGet() {
        WeakValueLinkedHashMap<Object, Object> map = new WeakValueLinkedHashMap<>();
        final Object[] keys = { new Object(), new Object(), new Object() };
        final Object[] values = { new Object(), new Object(), new Object() };
        map.put(keys[0], values[0]);
        map.put(keys[1], values[1]);
        map.put(keys[2], values[2]);
        assertEquals(values[0], map.get(keys[0]));
        assertEquals(values[1], map.get(keys[1]));
        assertEquals(values[2], map.get(keys[2]));
    }

    @Test
    void putAndGetWithGC() {
        WeakValueLinkedHashMap<Object, Object> map = new WeakValueLinkedHashMap<>();
        final Object[] keys = { new Object(), new Object(), new Object() };
        final @Nullable Object[] values = { new Object(), new Object(), new Object() };
        map.put(keys[0], values[0]);
        map.put(keys[1], values[1]);
        map.put(keys[2], values[2]);
        assertEquals(values[0], map.get(keys[0]));
        assertEquals(values[1], map.get(keys[1]));
        assertEquals(values[2], map.get(keys[2]));
        values[1] = null;
        encourageGC(100);
        assertEquals(values[0], map.get(keys[0]));
        encourageGC(100);
        assertNull(map.get(keys[1]),
            "As value is no longer reachable the previous calls to gc should have " +
                "removed the entry from the map");
        assertEquals(values[2], map.get(keys[2]));
    }

    @Test
    void containsKey() {
        WeakValueLinkedHashMap<Object, Object> map = new WeakValueLinkedHashMap<>();
        final Object[] keys = { new Object(), new Object(), new Object() };
        var a = new Object();
        var b = new Object();
        var c = new Object();

        map.put(keys[0], a);
        map.put(keys[1], b);
        map.put(keys[2], c);
        assertTrue(map.containsKey(keys[0]));
        assertTrue(map.containsKey(keys[1]));
        assertTrue(map.containsKey(keys[2]));

        b = null;
        encourageGC(100);
        assertTrue(map.containsKey(keys[0]));
        encourageGC(100);
        assertFalse(map.containsKey(keys[1]),
            "As value is no longer reachable the previous calls to gc should have " +
                "removed the entry from the map");
        assertTrue(map.containsKey(keys[2]));
    }
}

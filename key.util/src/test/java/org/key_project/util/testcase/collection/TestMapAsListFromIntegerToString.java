/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.util.testcase.collection;

import org.key_project.util.collection.DefaultImmutableMap;
import org.key_project.util.collection.ImmutableMap;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

/**
 * JUnit test for MapAsList<Integer,String> implementation
 */


public class TestMapAsListFromIntegerToString {

    private String[] entryStr;
    private Integer[] entryInt;

    /**
     * puts i and str in the corresponding arrays at place nr
     */
    private void put(int nr, int i, String str) {
        entryInt[nr] = i;
        entryStr[nr] = str;
    }

    @BeforeEach
    public void setUp() {
        entryStr = new String[4];
        entryInt = new Integer[4];
        put(0, 0, "Null");
        put(1, 1, "Eins");
        put(2, 2, "Zwei");
        put(3, 3, "Drei");
    }

    private ImmutableMap<Integer, String> createMap() {
        ImmutableMap<Integer, String> map = DefaultImmutableMap.nilMap();
        // create map with entrys like (1,"Eins")
        for (int i = 0; i < entryStr.length; i++) {
            map = map.put(entryInt[i], entryStr[i]);
        }
        return map;
    }

    @Test
    public void testMapEntriesAreTheSameThatHaveBeenPutInside() {
        ImmutableMap<Integer, String> map = createMap();
        // assert that all entries are in list
        for (int i = 0; i < entryStr.length; i++) {
            assertEquals(entryStr[i], map.get(entryInt[i]),
                "Map does not contain entry(" + entryInt[i] + ", " + entryStr[i] + ")");
        }
    }

    @Test
    public void testReplaceIfSameKeyWithNewValueIsPutInMap() {
        ImmutableMap<Integer, String> map = createMap();
        map = map.put(0, "Zero");
        // zero is in list
        assertTrue(map.containsValue("Zero"), "Zero is not in list.");
        // but not so old element Null with same key (0)
        assertFalse(map.containsValue("Null"),
            "Null is in list but should have been replaced by Zero");
    }

    @Test
    public void testImmutability() {
        ImmutableMap<Integer, String> map = createMap();
        ImmutableMap<Integer, String> old = map;
        map = map.put(5, "Fuenf");
        // 5 is in map but not in old
        assertTrue(map.containsValue("Fuenf"), "Fuenf is not in map");
        assertFalse(old.containsValue("Fuenf"),
            "Fuenf is in old map, but it should not be there. Map is not immutable.");
    }

    @Test
    public void testMapCanContainSameValueWithDifferentKeys() {
        ImmutableMap<Integer, String> map = createMap();
        // add a mapping with a value that has been mapped to
        // another key before
        Integer hundred = 100;
        map = map.put(hundred, entryStr[1]);
        assertSame(map.get(hundred), entryStr[1],
            entryStr[1] + " is not mapped to the newer key 100");
        assertSame(map.get(entryInt[1]), entryStr[1],
            entryStr[1] + " is not mapped to the older key " + entryInt[1]);
    }

    @Test
    public void testRemoveOneMappingWithSpecifiedKey() {
        ImmutableMap<Integer, String> map = createMap();
        // delete map (1,"Eins")
        map = map.remove(entryInt[1]);
        assertFalse(map.containsKey(entryInt[1]), "Deleted Mapping found in map");
    }

    @Test
    public void testRemoveAllMappingToSpecifiedValue() {
        ImmutableMap<Integer, String> map = createMap();
        // add a mapping with a value that has been mapped to
        // another key before
        Integer hundred = 100;
        map = map.put(hundred, entryStr[1]);
        // delete map (*,"Eins")
        map = map.removeAll(entryStr[1]);
        assertFalse(map.containsValue(entryStr[1]),
            "Value :" + entryStr[1] + " found in map. But I deleted all" + " of these values :-(");
    }

    @Test
    public void testSpecialCases() {
        ImmutableMap<Integer, String> map = DefaultImmutableMap.nilMap();
        map = map.put(0, "A");
        assertTrue(map.remove(0).isEmpty(),
            "Map should be empty and therefore equal to the EMPTY_MAP");

        assertTrue(map.remove(0).remove(0).isEmpty(),
            "Repeated key removal should not change anything");


        map = map.put(0, "B");
        assertTrue(map.size() == 1 && "B".equals(map.get(0)),
            "Map should have only one element with key 0 and value \"B\" ");


        map = map.removeAll("B");
        assertTrue(map.isEmpty(), "Map should be empty");


        map = map.put(0, "B");
        map = map.put(1, "C");
        map = map.put(2, "B");

        map = map.removeAll("B");
        assertTrue(map.size() == 1 && !map.containsValue("B"),
            "Map should not contain value \"B\" any longer ");

        map = map.removeAll("B");
        assertTrue(map.size() == 1 && !map.containsValue("B"),
            "Removing non-existant values should not change anything");

    }


}

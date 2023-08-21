/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.util.testcase.collection;

import java.util.Iterator;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableSet;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

/**
 * tests non-destructive Set implementation with String
 */

public class TestSetAsListOfString {

    final String[] str = new String[] { "Dies", "ist", "ein", "Test" };

    // test if String is SAME as one in the array arr
    private boolean isInArray(String str, String[] arr) {
        for (String anArr : arr) {
            if (anArr == str) {
                return true;
            }
        }
        return false;
    }


    // tests add and implicitly iterator, size
    @Test
    public void testAdd() {
        @SuppressWarnings("unchecked")
        ImmutableSet<String>[] newSet = new ImmutableSet[str.length + 1];
        newSet[0] = DefaultImmutableSet.nil();

        for (int i = 1; i < str.length + 1; i++) {
            newSet[i] = newSet[i - 1].add(str[i - 1]);
        }
        // Test elements in set
        for (int i = 0; i < str.length + 1; i++) {
            Iterator<String> it = newSet[i].iterator();
            int size = newSet[i].size();
            if (i > 0) { // set should have elements
                assertTrue(it.hasNext(), "Set has no elements, but should have some.");
                assertEquals(size, i, "Wrong cardinality");
            } else { // set is empty
                assertFalse(it.hasNext(), "Elements but set should be empty.");
                assertEquals(0, size, "Wrong cardinality.");
            }
            int nr = 0;
            while (it.hasNext()) {
                assertTrue(isInArray(it.next(), str), "Set has wrong elements");
                nr++;
            }
            // has right number of elements
            assertEquals(nr, size, "Set has iterated to less/often");
        }

        // add existing element, has to be SAME set
        assertSame(newSet[str.length], newSet[str.length].add(str[0]),
            "Element found 2 times in set or set is not the same.");
    }

    // tests unify
    @Test
    public void testUnion() {
        @SuppressWarnings("unchecked")
        ImmutableSet<String>[] newSet = new ImmutableSet[str.length + 1];
        newSet[0] = DefaultImmutableSet.<String>nil().add(str[0]).add(str[1]);
        newSet[1] = DefaultImmutableSet.<String>nil().add(str[1]).add(str[2]);
        // make the union of two sets and check if in the unions
        // appearance of str[1] == 1
        ImmutableSet<String> union = newSet[1].union(newSet[0]);
        assertEquals(3, union.size());
        // test if set has all elements
        for (int i = 0; i < 3; i++) {
            assertTrue(union.contains(str[0]));
        }
        // just to check that contains can say no too
        assertFalse(union.contains(str[3]));
    }

    @Test
    public void testUnionEmptyWithNonEmptySet() {
        ImmutableSet<String> empty = DefaultImmutableSet.nil();
        ImmutableSet<String> hal = DefaultImmutableSet.<String>nil().add("H").add("a").add("l");

        assertEquals(empty.union(hal), hal.union(empty), "Union of two sets should be symmetric");
        assertEquals(3, empty.union(hal).size(), "Wrong size.");
    }

    @Test
    public void testUnionRemoveDuplicates() {
        ImmutableSet<String> hal = DefaultImmutableSet.<String>nil().add("H").add("a").add("l");
        ImmutableSet<String> lo = DefaultImmutableSet.<String>nil().add("l").add("o");

        assertEquals(hal.union(lo), lo.union(hal), "Union of two sets should be symmetric");
        assertEquals(4, hal.union(lo).size(), "Wrong size.");
    }


    @Test
    public void testSubset() {
        ImmutableSet<String> subSet = DefaultImmutableSet.nil();
        ImmutableSet<String> superSet;
        // subSet={Dies,ist}
        // superSet={Dies,ist,ein}
        subSet = subSet.add(str[0]).add(str[1]);
        superSet = subSet.add(str[2]);
        assertTrue(subSet.subset(superSet), "Failure: in subset relation (!sub<super)");
        assertFalse(superSet.subset(subSet), "Failure: in subset relation (super<sub)");
        assertTrue(DefaultImmutableSet.<String>nil().subset(superSet),
            "EmptySet is not part of another Set");
        assertFalse(subSet.subset(DefaultImmutableSet.nil()),
            "A non empty set is subset of the empty set");
    }

    @Test
    public void testRemove() {
        ImmutableSet<String> set = DefaultImmutableSet.nil();
        // set={Dies,ist}
        set = set.add(str[0]).add(str[1]);
        assertFalse(set.remove(str[0]).contains(str[0]), "Did not remove " + str[0] + " from list");
    }


    @Test
    public void testToString() {
        ImmutableSet<String> newSet = DefaultImmutableSet.nil();
        for (int i = 0; i < str.length; i++) {
            newSet = newSet.add(str[str.length - 1 - i]);
        }
        assertEquals("{Dies,ist,ein,Test}", newSet.toString());
    }


}

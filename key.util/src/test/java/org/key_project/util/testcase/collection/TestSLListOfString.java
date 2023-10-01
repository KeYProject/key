/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.util.testcase.collection;

import java.util.Iterator;
import java.util.Objects;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import static org.junit.jupiter.api.Assertions.*;

/**
 * tests non-destructive list implementation with String
 */
public class TestSLListOfString {
    private static final Logger LOGGER = LoggerFactory.getLogger(TestSLListOfString.class);

    final String[] str = new String[] { "Dies", "ist", "ein", "Test" };

    ImmutableList<String> a; // "A" "B" "C"
    ImmutableList<String> a1; // "A" "B" "C"
    ImmutableList<String> b; // "A" "B"
    ImmutableList<String> c; // "A" "B" "C" "D"
    ImmutableList<String> d; // "A" "B" "A"
    ImmutableList<String> e; // "A" "B" null
    ImmutableList<String> e1; // "A" "B" null


    @BeforeEach
    public void setUp() {
        a = ImmutableSLList.<String>nil().prepend("C").prepend("B").prepend("A");
        a1 = ImmutableSLList.<String>nil().prepend("C").prepend("B").prepend("A");
        b = ImmutableSLList.<String>nil().prepend("B").prepend("A");
        c = ImmutableSLList.<String>nil().prepend("D").prepend("C").prepend("B").prepend("A");
        d = ImmutableSLList.<String>nil().prepend("A").prepend("B").prepend("A");
        e = ImmutableSLList.<String>nil().prepend((String) null).prepend("B").prepend("A");
        e1 = ImmutableSLList.<String>nil().prepend((String) null).prepend("B").prepend("A");
    }

    // tests prepend and implicitly iterator, size
    @Test
    public void testPrepend() {
        @SuppressWarnings("unchecked")
        ImmutableList<String>[] newList = new ImmutableList[str.length + 1];
        newList[0] = ImmutableSLList.nil();

        for (int i = 1; i < str.length + 1; i++) {
            newList[i] = newList[i - 1].prepend(str[i - 1]);
        }
        // Test elements in list
        for (int i = 0; i < str.length + 1; i++) {
            Iterator<String> it = newList[i].iterator();
            int size = newList[i].size();
            if (i > 0) { // list should have elements
                assertTrue(it.hasNext());
                assertEquals(size, i);
            } else { // list is empty
                assertFalse(it.hasNext());
                assertEquals(0, size);
            }
            int nr = 0;
            while (it.hasNext()) {
                assertSame(it.next(), str[size - 1 - nr]);
                nr++;
            }
            // list has right length
            assertEquals(nr, size);
        }
        // prepend two lists
        ImmutableList<String> prepList = newList[1].prepend(newList[2]);
        assertEquals(3, prepList.size());
        // right order
        assertEquals(str[1], prepList.head());
        assertEquals(str[0], prepList.tail().head());
        assertEquals(str[0], prepList.tail().tail().head());
    }

    // tests append and implicitly iterator, size
    @Test
    public void testAppend() {
        @SuppressWarnings("unchecked")
        ImmutableList<String>[] newList = new ImmutableList[str.length + 1];
        newList[0] = ImmutableSLList.nil();

        for (int i = 1; i < str.length + 1; i++) {
            newList[i] = newList[i - 1].append(str[i - 1]);
        }
        // Test elements in list
        for (int i = 0; i < str.length + 1; i++) {
            Iterator<String> it = newList[i].iterator();
            int size = newList[i].size();
            if (i > 0) { // list should have elements
                assertTrue(it.hasNext());
                assertEquals(size, i);
            } else { // list is empty
                assertFalse(it.hasNext());
                assertEquals(0, size);
            }
            int nr = 0;
            while (it.hasNext()) {
                assertSame(it.next(), str[nr]);
                nr++;
            }
            // list has right length
            assertEquals(nr, size);
        }

        // append two lists
        ImmutableList<String> appList = newList[2].append(newList[1]);
        assertEquals(3, appList.size());
        // right order
        assertEquals(str[0], appList.head());
        assertEquals(str[1], appList.tail().head());
        assertEquals(str[0], appList.tail().tail().head());
    }

    // tests tail,head
    @Test
    public void testHeadTail() {
        @SuppressWarnings("unchecked")
        ImmutableList<String>[] newList = new ImmutableList[str.length + 1];
        newList[0] = ImmutableSLList.nil();

        for (int i = 1; i < str.length + 1; i++) {
            newList[i] = newList[i - 1].prepend(str[i - 1]);
        }
        // test cascading tail
        for (int i = 0; i < str.length; i++) {
            assertSame(newList[i + 1].tail(), newList[i]);
            assertSame(newList[i + 1].head(), str[i]);
        }
    }

    // tests contains
    @Test
    public void testContains() {
        ImmutableList<String> newList = ImmutableSLList.nil();

        for (int i = 1; i < str.length + 1; i++) {
            newList = newList.append(str[i - 1]);
        }
        // test cascading tail
        for (String aStr : str) {
            assertTrue(newList.contains(aStr));
        }
    }


    // tests removeAll
    @Test
    public void testRemoveAll() {
        ImmutableList<String> newList = ImmutableSLList.nil();

        newList = newList.append(str[0]);
        for (int i = 1; i < str.length + 1; i++) {
            newList = newList.append(str[i - 1]);
        }
        newList = newList.append(str[0]);
        newList = newList.removeAll(str[0]);
        assertFalse(newList.contains(str[0]), "str[0] should have been removed");

    }

    @Test
    public void testRemoveFirst() {
        ImmutableList<String> newList = ImmutableSLList.nil();

        newList = newList.prepend(str[0]);
        for (int i = 1; i < str.length + 1; i++) {
            newList = newList.prepend(str[i - 1]);
        }
        newList = newList.prepend(str[0]);
        int oldSize = newList.size();
        newList = newList.removeFirst(str[0]);


        assertTrue(!Objects.equals(newList.head(), str[0]) && newList.size() == oldSize - 1,
            "Only first occurrence should have been removed");

        newList = newList.removeFirst(str[0]);
        assertEquals(newList.size(), oldSize - 2, "Only first occurrence should have been removed");
        newList = newList.removeFirst(str[0]);

        assertTrue(!(newList.contains(str[0])) && newList.size() == oldSize - 3,
            "Only first occurrence should have been removed");

    }

    @Test
    public void testEquals() {
        assertEquals(a, a1, "a==a1");
        assertNotEquals(a, b, "a!=b");
        assertNotEquals(a, c, "a!=c");
        assertNotEquals(a, d, "a!=d");
        assertNotEquals(a, e, "a!=e");
        assertNotEquals(e, a, "e!=a");
        assertEquals(e, e1, "e==e1");
    }


    @Test
    public void testToString() {
        ImmutableList<String> newList = ImmutableSLList.nil();
        for (String aStr : str) {
            newList = newList.append(aStr);
        }
        assertEquals("[Dies,ist,ein,Test]", newList.toString());
    }


    public static void performanceTest(int n) {
        LOGGER.info("Performance Test for " + n + " elements");
        ImmutableList<String> newList = ImmutableSLList.nil();
        LOGGER.info("Create list with prepend.");
        long start = System.currentTimeMillis();
        for (int i = 0; i < n; i++) {
            newList = newList.prepend("" + i);
        }
        long end = System.currentTimeMillis();
        LOGGER.info("Time:" + (end - start) + " ms");

        start = System.currentTimeMillis();
        for (int i = 0; i < n; i++) {
            newList = newList.append("" + i);
        }
        end = System.currentTimeMillis();
        LOGGER.info("append: {} ms ", end - start);

        start = System.currentTimeMillis();
        newList.contains("" + n);
        end = System.currentTimeMillis();
        LOGGER.info("contains: {} ms", end - start);
    }


    public static void main(String[] args) {
        ImmutableList<String> newList = ImmutableSLList.nil();
        newList.prepend("a");

        performanceTest(10);
        performanceTest(100);
        performanceTest(1000);
        performanceTest(10000);
        performanceTest(100000);
        performanceTest(1000000);
    }
}

/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.util.testcase.collection;

import java.util.Arrays;
import java.util.Iterator;
import java.util.Random;

import org.key_project.util.ExtList;
import org.key_project.util.collection.ImmutableHeap;
import org.key_project.util.collection.ImmutableLeftistHeap;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertTrue;

public class TestLeftistHeapOfInteger {

    ImmutableList<Integer> a;
    ImmutableList<Integer> b;

    final Random rand = new Random();

    @BeforeEach
    public void setUp() {
        a = ImmutableSLList.<Integer>nil().prepend(13).prepend(20).prepend(5).prepend(7).prepend(16)
                .prepend(60).prepend(20).prepend(-34);
        b = ImmutableSLList.<Integer>nil().prepend(-1000).prepend(1000).prepend(8);
    }

    @Test
    public void testInsertElements() {
        ImmutableHeap<Integer> h = ImmutableLeftistHeap.nilHeap();
        assertTrue(h.isEmpty() && h.size() == 0, "Empty heap should be empty");

        h.insert(1);
        assertTrue(h.isEmpty() && h.size() == 0, "Empty heap should be empty");

        h = h.insert(1);
        assertTrue(!h.isEmpty() && h.size() == 1 && h.findMin() == 1,
            "Heap should contain one element");

        h = h.deleteMin();
        assertTrue(h.isEmpty() && h.size() == 0, "Empty heap should be empty");

        h = h.insert(1).insert(2);
        assertTrue(!h.isEmpty() && h.size() == 2 && h.findMin() == 1,
            "Heap should contain two elements");
        h = h.deleteMin();
        assertTrue(!h.isEmpty() && h.size() == 1 && h.findMin() == 2,
            "Heap should contain one element");
        h = h.deleteMin();
        assertTrue(h.isEmpty() && h.size() == 0, "Empty heap should be empty");
    }

    private boolean equals(Iterator<Integer> t0, Iterator<Integer> t1) {
        ExtList l0 = new ExtList(), l1 = new ExtList();

        while (t0.hasNext()) {
            l0.add(t0.next());
        }

        while (t1.hasNext()) {
            l1.add(t1.next());
        }

        Object[] a0 = l0.collect(Object.class);
        Object[] a1 = l1.collect(Object.class);

        Arrays.sort(a0);
        Arrays.sort(a1);

        return Arrays.equals(a0, a1);
    }

    private void checkHeap(ImmutableList<Integer> elements, ImmutableHeap<Integer> h) {
        assertTrue(h.size() == elements.size() && (h.size() == 0) == h.isEmpty(),
            "Heap has incorrect size");

        assertTrue(equals(h.iterator(), elements.iterator()),
            "Unsorted heap iterator does not return the right elements");

        Iterator<Integer> t0 = h.sortedIterator();
        Integer lastElement = null;
        Integer element;

        while (t0.hasNext()) {
            element = t0.next();
            if (lastElement != null) {
                assertTrue(lastElement.compareTo(element) <= 0,
                    "Elements returned by sorted iterator should be sorted");
            }
            lastElement = element;
        }

        assertTrue(equals(h.sortedIterator(), elements.iterator()),
            "Unsorted heap iterator does not return the right elements");

        ImmutableList<Integer> list = ImmutableSLList.nil();
        lastElement = null;

        while (!h.isEmpty()) {
            element = h.findMin();
            list = list.prepend(element);
            if (lastElement != null) {
                assertTrue(lastElement.compareTo(element) <= 0,
                    "Elements returned by findMin() should be sorted");
            }
            lastElement = element;
            h = h.deleteMin();
        }

        assertTrue(equals(list.iterator(), elements.iterator()),
            "findMin does not return the right elements");
    }

    private ImmutableHeap<Integer> removeAll(ImmutableHeap<Integer> h, Iterator<Integer> elements) {
        while (elements.hasNext()) {
            h = h.removeAll(elements.next());
        }
        return h;
    }

    @Test
    public void testInsertIterator() {
        ImmutableHeap<Integer> h = ImmutableLeftistHeap.nilHeap();

        h = h.insert(ImmutableSLList.<Integer>nil().iterator());
        checkHeap(ImmutableSLList.nil(), h);
        assertTrue(h.isEmpty() && h.size() == 0, "Empty heap should be empty");

        h = h.insert(a.iterator());
        checkHeap(a, h);

        h = h.insert(a.iterator());
        checkHeap(a.prepend(a), h);

        h = h.insert(ImmutableSLList.<Integer>nil().iterator());
        checkHeap(a.prepend(a), h);

        h = h.insert(h.iterator());
        checkHeap(a.prepend(a).prepend(a).prepend(a), h);

        h = h.insert(h.sortedIterator());
        checkHeap(a.prepend(a).prepend(a).prepend(a).prepend(a).prepend(a).prepend(a).prepend(a),
            h);
    }

    @Test
    public void testInsertHeap() {
        ImmutableHeap<Integer> h = ImmutableLeftistHeap.nilHeap();

        h = h.insert(a.iterator());
        checkHeap(a, h);

        h = h.insert(ImmutableLeftistHeap.nilHeap());
        checkHeap(a, h);

        h = h.insert(h);
        checkHeap(a.prepend(a), h);

        h = h.insert(ImmutableLeftistHeap.<Integer>nilHeap().insert(123));
        checkHeap(a.prepend(a).prepend(123), h);
    }

    @Test
    public void testRemoveAll() {
        ImmutableHeap<Integer> h = ImmutableLeftistHeap.nilHeap();

        // Test removal of all elements (from empty heap)
        checkHeap(ImmutableSLList.nil(), removeAll(h, a.iterator()));

        h = h.insert(a.iterator());
        checkHeap(a, h);

        // Test removal of arbitrary elements
        checkHeap(a.removeAll(a.head()), h.removeAll(a.head()));

        // Test removal of all elements
        checkHeap(ImmutableSLList.nil(), removeAll(h, a.iterator()));

        // Test removal of non-existing elements
        assertSame(h, removeAll(h, b.iterator()), "Heap should not be different");
    }

    @Test
    public void testLargeHeap() {
        ImmutableHeap<Integer> h = ImmutableLeftistHeap.nilHeap();
        ImmutableList<Integer> l = ImmutableSLList.nil();

        int i = 1000;
        while (i-- != 0) {
            l = l.prepend(rand.nextInt(1000000));
        }

        h = h.insert(l.iterator());

        checkHeap(l, h);
    }

}

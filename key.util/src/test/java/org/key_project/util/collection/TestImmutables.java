/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.util.collection;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

public class TestImmutables {

    @Test
    public void testRemoveDuplicatesLarge() {
        ImmutableList<Integer> l = ImmutableSLList.nil();
        for (int i = 0; i < 100; i++) {
            l = l.prepend((i * 2) % 160);
        }

        assertEquals(100, l.size());
        assertFalse(Immutables.isDuplicateFree(l));

        ImmutableList<Integer> cleaned = Immutables.removeDuplicates(l);
        assertEquals(80, cleaned.size());

        assertTrue(Immutables.isDuplicateFree(cleaned));

        l = cleaned;
        for (int i = 79; i >= 0; i--) {
            assertEquals(i * 2, l.head().intValue());
            l = l.tail();
        }
    }

    @Test
    public void testRemoveDuplicates() {

        String[][] a = { { "a", "b", "a", "c", "d", "d", "a", "e" }, { null, "a", null },
            { "1", "1", "1", "1", "1" } };

        String[][] expected = { { "a", "b", "c", "d", "e" }, { null, "a" }, { "1" } };

        for (int i = 0; i < a.length; i++) {
            ImmutableList<String> l = ImmutableSLList.<String>nil().prepend(a[i]).reverse();

            assertFalse(Immutables.isDuplicateFree(l));

            ImmutableList<String> cleaned = Immutables.removeDuplicates(l);
            String[] a2 = cleaned.reverse().toArray(String.class);


            assertTrue(Immutables.isDuplicateFree(cleaned));
            assertDeepEquals(expected[i], a2);
        }
    }

    @Test
    public void testRemoveDuplicatesIdentical() {
        String[] a = { "a", "b", "c", "d", "e" };
        ImmutableList<String> l = ImmutableSLList.<String>nil().prepend(a);

        ImmutableList<String> cleaned = Immutables.removeDuplicates(l);

        assertSame(l, cleaned);
    }

    @Test
    public void testIsDuplicateFree() {
        String[][] a = { { "a", "b", "c", "d", "e" }, {}, { "a" }, { null }, { null, "a" } };

        for (String[] strings : a) {
            ImmutableList<String> l = ImmutableSLList.<String>nil().prepend(strings);
            assertTrue(Immutables.isDuplicateFree(l));
        }

        String[][] b = { { "a", "a" }, { "a", "b", "c", "d", "a" }, { "a", "b", "a", "d", "e" },
            { "a", "b", "d", "d", "e" }, { "a", "b", "c", "d", "d" }, { null, "a", null } };

        for (String[] strings : b) {
            ImmutableList<String> l = ImmutableSLList.<String>nil().prepend(strings);
            assertFalse(Immutables.isDuplicateFree(l));
        }


    }

    private static void assertDeepEquals(Object[] expected, Object[] array) {
        assertEquals(expected.length, array.length);
        for (int i = 0; i < array.length; i++) {
            assertEquals(expected[i], array[i]);
        }
    }

    @Test
    public void testUnion() {
        for (int setSize = 0; setSize < DefaultImmutableSet.UNION_OPTIMIZATION_SIZE * 2
                + 2; setSize++) {
            ImmutableSet<Integer> s1 = DefaultImmutableSet.nil();
            ImmutableSet<Integer> s2 = DefaultImmutableSet.nil();
            ImmutableSet<Integer> s1UnionS2 = DefaultImmutableSet.nil();
            for (int i = 0; i < setSize; i++) {
                s1 = s1.add(i);
                s2 = s2.add(i * -1);
                s1UnionS2 = s1UnionS2.add(i);
                s1UnionS2 = s1UnionS2.add(i * -1);
            }
            // Test union without duplicates
            ImmutableSet<Integer> union = s1.union(s2);
            assertEquals(s1UnionS2, union);
            // Test union with duplicates
            union = union.union(s1);
            assertEquals(s1UnionS2, union);
            union = union.union(s2);
            assertEquals(s1UnionS2, union);
            union = union.union(union);
            assertEquals(s1UnionS2, union);
            // Test union without duplicates (other way round)
            union = s2.union(s1);
            assertEquals(s1UnionS2, union);
            // Test union with duplicates
            union = union.union(s1);
            assertEquals(s1UnionS2, union);
            union = union.union(s2);
            assertEquals(s1UnionS2, union);
            union = union.union(union);
            assertEquals(s1UnionS2, union);
        }
    }

    @Test
    public void testEqualityEmpty() {
        ImmutableSet<Object> s1 = DefaultImmutableSet.nil();
        ImmutableSet<Object> s2 = DefaultImmutableSet.fromImmutableList(ImmutableSLList.nil());
        assertEquals(0, s1.size());
        assertEquals(0, s2.size());

        assertEquals(s1, s2);
    }

    @Test
    public void testIntersectEmpty() {
        ImmutableSet<Object> s0 = DefaultImmutableSet.nil();
        ImmutableSet<Object> s1 = DefaultImmutableSet.nil().add("1");
        ImmutableSet<Object> s2 = DefaultImmutableSet.nil().add("2");

        ImmutableSet<Object> sIntersect = s1.intersect(s2);
        assertEquals(0, sIntersect.size());
        assertEquals(s0, sIntersect);
    }

    @Test
    public void testHashCodes() {

        ImmutableSet<Object> s1 = DefaultImmutableSet.nil().add("one").add("two");
        ImmutableSet<Object> s2 = DefaultImmutableSet.nil().add("two").add("one");

        assertEquals(s1, s2);
        int hash1 = s1.hashCode();
        int hash2 = s2.hashCode();
        assertEquals(hash1, hash2);
    }

    @Test
    public void testFilter() {
        ImmutableList<Integer> l = ImmutableList.of(1, 2, 3, 4, 5, 6, 7, 8, 9);
        ImmutableList<Integer> filtered = Immutables.filter(l, n -> n % 2 == 0);
        assertEquals(ImmutableList.of(2, 4, 6, 8), filtered);
    }

    @Test
    public void testFilterStackoverflow() {
        // With the original tail recursive implementation, this would give
        // an overflow --> made it a loop.
        ImmutableList<Integer> l = ImmutableSLList.nil();
        for (int i = 0; i < 1_000_000; i++) {
            l = l.prepend(i);
        }

        ImmutableList<Integer> filtered = Immutables.filter(l, n -> n % 2 == 0);
        assertEquals(500_000, filtered.size());
    }

    @Test
    public void testMap() {
        ImmutableList<Integer> l = ImmutableList.of(1, 2, 3, 4);
        ImmutableList<Boolean> mapped = Immutables.map(l, n -> n % 2 == 0);
        assertEquals(ImmutableList.of(false, true, false, true), mapped);
    }

    @Test
    public void testMapStackoverflow() {
        // With the original tail recursive implementation, this would give
        // an overflow --> made it a loop.
        ImmutableList<Integer> l = ImmutableSLList.nil();
        for (int i = 0; i < 1_000_000; i++) {
            l = l.prepend(i);
        }

        ImmutableList<Boolean> mapped = Immutables.map(l, n -> n % 2 == 0);
        assertEquals(1_000_000, mapped.size());
    }

    @Test
    public void testExistsStackoverflow() {
        // With a tail recursive implementation, this would give
        // an overflow --> it is a loop.
        ImmutableList<Integer> l = ImmutableSLList.nil();
        for (int i = 0; i < 1_000_000; i++) {
            l = l.prepend(i);
        }

        boolean result = l.exists(x -> x == 999_998);
        assertTrue(result);
        result = l.exists(x -> x == 1_999_998);
        assertFalse(result);
    }

}

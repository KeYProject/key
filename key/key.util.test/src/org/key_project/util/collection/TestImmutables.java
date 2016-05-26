package org.key_project.util.collection;

import junit.framework.TestCase;

import org.junit.Test;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;
import org.key_project.util.collection.Immutables;

public class TestImmutables extends TestCase {

    @Test
    public void testRemoveDuplicatesLarge() {
        ImmutableList<Integer> l = ImmutableSLList.<Integer>nil();
        for(int i = 0; i < 100; i++) {
            l = l.prepend((i * 2) % 160);
        }

        assertEquals(100, l.size());
        assertFalse(Immutables.isDuplicateFree(l));

        ImmutableList<Integer> cleaned = Immutables.removeDuplicates(l);
        assertEquals(80, cleaned.size());

        assertTrue(Immutables.isDuplicateFree(cleaned));

        l = cleaned;
        for (int i = 79; i >= 0; i--) {
            assertEquals(i*2, l.head().intValue());
            l = l.tail();
        }
    }

    @Test
    public void testRemoveDuplicates() {

        String[][] a = {
                { "a", "b", "a", "c", "d", "d", "a", "e" },
                { null, "a" , null },
                { "1", "1", "1", "1", "1" }
        };

        String[][] expected = {
                { "a", "b", "c", "d", "e" },
                { null, "a" },
                { "1" }
        };

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
    public void testIsDuplicateFree() throws Exception {
        String[][] a = { { "a", "b", "c", "d", "e" },
                {  }, {"a"}, { null }, { null, "a" } };

        for (String[] strings : a) {
            ImmutableList<String> l = ImmutableSLList.<String>nil().prepend(strings);
            assertTrue(Immutables.isDuplicateFree(l));
        }

        String[][] b = { { "a", "a"},
                { "a", "b", "c", "d", "a" },
                { "a", "b", "a", "d", "e" },
                { "a", "b", "d", "d", "e" },
                { "a", "b", "c", "d", "d" },
                { null, "a", null }};

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

    public void testImprovedSetUnion() {
        String[][] a = { { "a", "b", "c", "d"}, { "a", "b2", "c", "d3"},
                { "a", "b", "a", "d", "e" }, { "a", "b", "d", "d", "e" },
                { "a" }, { },
                { "a", "b", "c" }, {"c","a", "b" } ,
                { null, "a"}, { "b" } };

        for (int i = 0; i < a.length; i+=2) {
            ImmutableSet<String> s1 = DefaultImmutableSet.<String>nil();
            for (int j = 0; j < a[i].length; j++) {
                s1 = s1.add(a[i][j]);
            }
            ImmutableSet<String> s2 = DefaultImmutableSet.<String>nil();
            for (int j = 0; j < a[i+1].length; j++) {
                s2 = s2.add(a[i+1][j]);
            }

            DefaultImmutableSet<String> newUnion = ((DefaultImmutableSet<String>) s1).newUnion(s2);
            DefaultImmutableSet<String> oldUnion = ((DefaultImmutableSet<String>) s2).originalUnion(s1);
            assertEquals(oldUnion, newUnion);

            newUnion = ((DefaultImmutableSet<String>) s2).newUnion(s1);
            oldUnion = ((DefaultImmutableSet<String>) s2).originalUnion(s1);
            assertEquals(oldUnion, newUnion);
        }

    }

    public void testEqualityEmpty() throws Exception {
        ImmutableSet<Object> s1 = DefaultImmutableSet.<Object>nil();
        ImmutableSet<Object> s2 = DefaultImmutableSet.fromImmutableList(ImmutableSLList.nil());
        assertEquals(0, s1.size());
        assertEquals(0, s2.size());

        assertEquals(s1,s2);
    }

    public void testIntersectEmpty() {
        ImmutableSet<Object> s0 = DefaultImmutableSet.<Object>nil();
        ImmutableSet<Object> s1 = DefaultImmutableSet.<Object>nil().add("1");
        ImmutableSet<Object> s2 = DefaultImmutableSet.<Object>nil().add("2");

        ImmutableSet<Object> sIntersect = s1.intersect(s2);
        assertEquals(0, sIntersect.size());
        assertEquals(s0, sIntersect);
    }

    public void testHashCodes() {

        ImmutableSet<Object> s1 = DefaultImmutableSet.<Object>nil().add("one").add("two");
        ImmutableSet<Object> s2 = DefaultImmutableSet.<Object>nil().add("two").add("one");

        assertEquals(s1, s2);
        int hash1 = s1.hashCode();
        int hash2 = s2.hashCode();
        assertEquals(hash1, hash2);
    }

}

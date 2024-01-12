package org.key_project.util.collection;

import static org.junit.Assert.*;

import org.junit.Test;

public class TestSLList {

    @Test
    public void testRemoveAll() {
        ImmutableList<Object> l = ImmutableSLList.nil().prepend(1,2,1,2);

        assertEquals("[1,1]", l.removeAll(2).toString());
    }

    @Test
    public void testMap() {
        ImmutableList<Integer> l = ImmutableSLList.<Integer>nil().prepend(1,2,-1,-2);

        assertEquals("[1,4,1,4]", l.map(x -> x*x).toString());
    }

    @Test
    public void testReplace() {
        ImmutableList<Integer> l = ImmutableSLList.<Integer>nil().prepend(1,2,3,4);

        assertEquals("[1,2,0,4]", l.replace(2, 0).toString());
        assertEquals("[0,2,3,4]", l.replace(0, 0).toString());
        assertEquals("[1,2,3,0]", l.replace(3, 0).toString());
    }

    @Test(expected = IndexOutOfBoundsException.class)
    public void testReplaceBounds1() {
        ImmutableList<Integer> l = ImmutableSLList.<Integer>nil().prepend(1,2,3,4);

        System.out.println(l.replace(-1, 0));
    }

    // revealed a bug
    @Test(expected = IndexOutOfBoundsException.class)
    public void testReplaceBounds2() {
        ImmutableList<Integer> l = ImmutableSLList.<Integer>nil().prepend(1,2,3,4);

        System.out.println(l.replace(4, 0));
    }

}

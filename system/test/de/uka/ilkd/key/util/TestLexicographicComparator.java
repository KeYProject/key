package de.uka.ilkd.key.util;

import junit.framework.TestCase;

public class TestLexicographicComparator extends TestCase {

    
    public void testCompareInt() {
        Integer[] a = {3,4};
        Integer[] b = {1,7};
        final LexicographicComparator<Integer> lcc = new LexicographicComparator<Integer>();
        assertEquals(-1,lcc.compare(a,b));
        b = new Integer[]{3,4,0};
        assertEquals(1,lcc.compare(a, b));
        a = new Integer[]{3,4,0};
        assertEquals(0,lcc.compare(a,b));
    }
}

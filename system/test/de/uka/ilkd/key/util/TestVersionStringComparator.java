package de.uka.ilkd.key.util;

import junit.framework.TestCase;


public class TestVersionStringComparator extends TestCase {
    
    public void test0 () {
        final VersionStringComparator vsc = new VersionStringComparator();
        int r = vsc.compare("1.9.3777", "2.4.0");
        assertTrue(r > 0);
    }

    public void test1 () {
        final VersionStringComparator vsc = new VersionStringComparator();
        int r = vsc.compare("2.4.0", "2.4.0");
        assertTrue(r == 0);
    }
    
    public void test2 () {
        final VersionStringComparator vsc = new VersionStringComparator();
        int r = vsc.compare("not a number", "2.4.0");
        assertTrue(r > 0);
    }
    
    public void test3 () {
        final VersionStringComparator vsc = new VersionStringComparator();
        int r = vsc.compare("2.4-special", "2.4.1");
        assertTrue(r > 0);
    }
   
    public void test4 () {
        final VersionStringComparator vsc = new VersionStringComparator();
        int r = vsc.compare("1-9$3777", "2/4*0");
        assertTrue(r > 0);
    }
}

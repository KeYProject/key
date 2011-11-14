package de.uka.ilkd.key.util;


import junit.framework.TestCase;

public class TestMiscTools extends TestCase {

    public void testDisectFilename() {
        String s = "/home/daniel//workspace/key";
        Object[] ls = MiscTools.disectFilename(s).toArray();
        assertEquals("",ls[0]);
        assertEquals("key",ls[4]);
        s = s.substring(1);
        ls = MiscTools.disectFilename(s).toArray();
        assertEquals("home",ls[0]);
//        s = "C:\\Windows\\Users\\";
//        ls = MiscTools.disectFilename(s).toArray();
//        assertEquals("",ls[0]);
        s = s+"/";
        ls = MiscTools.disectFilename(s).toArray();
        assertEquals(4,ls.length);
        assertEquals("key",ls[3]);
    }

}

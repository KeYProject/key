package de.uka.ilkd.key.util;


import junit.framework.TestCase;
import static de.uka.ilkd.key.util.MiscTools.*;

public class TestMiscTools extends TestCase {

    public void testDisectFilename() {
        String s = "/home/daniel//workspace/key";
        Object[] ls = MiscTools.disectFilename(s).toArray();
        assertEquals("",ls[0]);
        assertEquals("key",ls[4]);
        s = s.substring(1);
        ls = MiscTools.disectFilename(s).toArray();
        assertEquals("home",ls[0]);
        s = s+"/";
        ls = MiscTools.disectFilename(s).toArray();
        assertEquals(4,ls.length);
        assertEquals("key",ls[3]);
        s = "."+s;
        ls = MiscTools.disectFilename(s).toArray();
        assertEquals(4,ls.length);
        assertEquals("key",ls[3]);
        // test windows delimiters
        s = "C:\\Windows\\Users\\";
        ls = MiscTools.disectFilename(s).toArray();
        assertEquals("C:",ls[0]);
    }
    
    public void testMakeFilenameRelative(){
        String s = "/home/daniel/bla";
        String t = "/home/daniel/blubb";
        String u = MiscTools.makeFilenameRelative(s,t);
        assertEquals("../bla",u);
        // s shorter than t
        t = "/home/daniel/bla/foo/bar";
        u = MiscTools.makeFilenameRelative(s, t);
        assertEquals("../..",u);
        // s already relative
        s = s.substring(1);
        assertEquals(s,MiscTools.makeFilenameRelative(s, t));
        s = "/home/../home/daniel/";
        t = "/home";
        assertEquals("daniel", MiscTools.makeFilenameRelative(s, t));
        
        // test windows delimiters
        s = "C:\\Windows";
        t = "c:\\";
        u = MiscTools.makeFilenameRelative(s, t);
        assertEquals("Windows",u);
        // do stupid things
        try {
            t = "/home/daniel";
            u = MiscTools.makeFilenameRelative(s, t);
            fail();
        } catch (RuntimeException e){
            assertTrue(true);
        }
    }
    
    public void testToValidFileName(){
        assertEquals("foo_bar", MiscTools.toValidFileName("foo:bar"));
        assertEquals("foo_bar", MiscTools.toValidFileName("foo\\bar"));
        assertEquals("foo(bar)", MiscTools.toValidFileName("foo[bar]"));
    }
    
    public void testContainsWholeWord(){
        assertTrue(containsWholeWord("foo bar","foo"));
        assertTrue(containsWholeWord("foo;","foo"));
        assertTrue(containsWholeWord("\rfoo\t","foo"));
        assertTrue(containsWholeWord(" foo foo","foo"));
        assertFalse(containsWholeWord("foobar","foo"));
        assertFalse(containsWholeWord("bar","foo"));
    }
    
    public void testIsJMLComment(){
        assertTrue(isJMLComment("/*@iarijagjs"));
        assertTrue(isJMLComment("//@ sasahgue"));
        assertTrue(isJMLComment("//+KeY@"));
        assertTrue(isJMLComment("//-ESC@"));
        assertFalse(isJMLComment("//-KeY@"));
        assertFalse(isJMLComment("// @"));
        assertFalse(isJMLComment("/*"));
        assertFalse(isJMLComment("/**"));
    }
}

package de.uka.ilkd.key.logic;

import junit.framework.TestCase;

public class TestName extends TestCase {

    protected void setUp() throws Exception {
        super.setUp();
    }

    public void testEquals (){
        Name n = new Name("test");
        Name m = new Name(new String("test"));
        assertEquals(n,m);
    }
}

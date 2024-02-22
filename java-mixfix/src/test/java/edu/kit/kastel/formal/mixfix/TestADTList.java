/*
 * Copyright (C) 2010 Universitaet Karlsruhe, Germany
 *    written by Mattias Ulbrich
 * 
 * The system is protected by the GNU General Public License. 
 * See LICENSE.TXT for details.
 */
package edu.kit.kastel.formal.mixfix;

import org.junit.Test;

import static org.junit.Assert.*;

/**
 * Test cases for the class {@link ADTList}.
 */
public class TestADTList {
    
    private ADTList<String> list123 = ADTList.<String>nil().cons("1").cons("2").cons("3");
    
    public void testEquals() throws Exception {
        
        ADTList<String> listCopy = ADTList.<String>nil().cons("1").cons("2").cons("3");
        ADTList<String> list1234 = listCopy.cons("4");
        
        assertTrue(ADTList.nil().equals(ADTList.nil()));
        assertTrue(list123.equals(listCopy));
        assertFalse(list123.equals(list1234));
    }
    
    @Test
    public void testToString() throws Exception {
        ADTList<String> list1 = ADTList.<String>nil().cons("1").cons("2").cons("3");
        assertEquals("[3,2,1]", list1.toString());
        assertEquals("[]", ADTList.nil().toString());
    }


    @Test
    public void testIterator() throws Exception {
        for (@SuppressWarnings("unused") Object o : ADTList.nil()) {
            fail("Must never be reached");
        }
        
        String s = "";
        for (String string : list123) {
            s = s + string;
        }
        assertEquals("321", s);
    }

    @Test
    public void testSize() throws Exception {
        assertEquals(0, ADTList.nil().size());
        assertEquals(3, list123.size());
    }

    @Test
    public void testRev() {
        ADTList<String> list321 = ADTList.<String>nil().cons("3").cons("2").cons("1");
        assertEquals(list321, list123.rev());
    }

}


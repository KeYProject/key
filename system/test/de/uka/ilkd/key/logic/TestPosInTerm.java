// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.logic;

import junit.framework.TestCase;

public class TestPosInTerm extends TestCase {
    
    
    public void testUpDownWithoutCopyExceptForTopLevelChange() {
        PosInTerm pit = PosInTerm.getTopLevel();
                
        pit = pit.down(8);
        assertTrue(pit.getIndex() == 8);
        assertTrue(pit.depth() == 1);
        
        
        PosInTerm copy = pit;
        
        pit = pit.down(20);
        assertTrue(pit.depth() == 2);
        assertTrue(pit.getIndex() == 20);

        
        assertTrue(!pit.equals(copy));        
        assertTrue(copy.getIndex() == 8);
        assertTrue(copy.depth() == 1);        
    
        pit = pit.up();
        assertEquals(copy, pit);   
        
        pit = pit.up();
        pit = pit.down(15);
        assertTrue(copy.getIndex() == 8);
        assertTrue(pit.getIndex() == 15);        
    }

    public void testCopyFlag() {
        PosInTerm pit = PosInTerm.getTopLevel();        
        pit = pit.down(10);
        
        PosInTerm copy = pit;        
        pit = pit.down(20);
        copy = copy.down(30);
        
        assertTrue(pit.getIndex() == 20); 
        assertTrue(copy.getIndex() == 30);                
    }
    
    public void testUpDownWithCopy() {
        int[] pos = new int[]{10, 2, 5, 20, 4, 100, 25, 65, 23, 40, 2, 0, 1, 0, 1};

        PosInTerm pit = toPosInTerm(pos);
                
        PosInTerm copy = pit;
        
        assertEquals(pos.length, pit.depth());
        
        for (int i = 0; i < pit.depth(); i++) {
            assertEquals(pos[i], pit.getIndexAt(i));
        }
        
        pit = pit.up().up().up();
        pit = pit.down(10000).down(1000);

        //old unchanged
        for (int i = 0; i < pit.depth(); i++) {
            assertEquals("PosInTerms should be immutable, but"
                    + "an old one was changed", copy.getIndexAt(i), pos[i]);
        }

        assertEquals(1000, pit.getIndex());
        assertEquals(10000, pit.up().getIndex());        
    }

    private PosInTerm toPosInTerm(int[] pos) {
        PosInTerm pit = PosInTerm.getTopLevel();

        for (int i : pos) {
            pit = pit.down(i);
        }
        return pit;
    }
    
    public void testEquals() {
        int[] pos = new int[]{10, 2, 5, 20, 4, 100, 25, 65, 23, 40, 2, 0, 1, 0, 1};
        int[] pos2 = new int[]{10, 2, 5, 20, 4, 100, 75, 65, 23, 40, 2, 0, 1, 0, 1};
        int[] pos3 = new int[]{10, 2, 5, 20, 4, 100, 25, 2, 0, 1, 0, 1};
        int[] pos4 = new int[]{10, 2, 5, 20, 4, 100, 25, 65, 23, 40, 2, 0, 1, 0, 1, 67, 68, 69};


        PosInTerm pit1 = toPosInTerm(pos);
        PosInTerm pit2 = toPosInTerm(pos);
        assertEquals(pit1, pit2);
        assertEquals(pit1.hashCode(), pit2.hashCode());
            
        assertFalse(pit1.equals(toPosInTerm(pos2)));
        assertFalse(pit1.equals(toPosInTerm(pos3)));
        assertFalse(pit1.equals(toPosInTerm(pos4)));
    }
    
    public void testFirstN() {
        int[] pos = new int[]{10, 2, 5, 20, 4, 100, 25, 65, 23, 40, 2, 0, 1, 0, 1};
        int[] posN4 = new int[]{10, 2, 5, 20};
        int[] posN7 = new int[]{10, 2, 5, 20, 4, 100, 25};
        
        PosInTerm pit = toPosInTerm(pos);

        PosInTerm pitN1 = PosInTerm.getTopLevel().down(10);
        PosInTerm pitN4 = toPosInTerm(posN4);
        PosInTerm pitN7 = toPosInTerm(posN7);

        assertTrue(pit.firstN(0).isTopLevel());
        assertEquals(pitN1, pit.firstN(1));
        assertEquals(pitN4, pit.firstN(4));
        assertEquals(pitN7, pit.firstN(7));
        assertEquals(pit, pit.firstN(pit.depth()));        
    }
    
    public void testIntegerList() {
        int[] pos = new int[]{10, 2, 5, 20, 4, 100, 25, 65, 23, 40, 2, 0, 1, 0, 1};
        
        PosInTerm pit = toPosInTerm(pos);
        
        assertEquals("[10,2,5,20,4,100,25,65,23,40,2,0,1,0,1]", pit.integerList(pit.iterator()));
        assertEquals("[1,0,1,0,2,40,23,65,25,100,4,20,5,2,10]", pit.integerList(pit.reverseIterator()));
    }
        
    public void testParseReverseString() {
        int[] pos = new int[]{10, 2, 5, 20, 4, 100, 25, 65, 23, 40, 2, 0, 1, 0, 1};
        
        PosInTerm pit = toPosInTerm(pos);
        
        assertEquals(pit, 
                PosInTerm.parseReverseString("1,0,1,0,2,40,23,65,25,100,4,20,5,2,10"));
        
    }
    
}
/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

public class TestPosInTerm {


    @Test
    public void testUpDownWithoutCopyExceptForTopLevelChange() {
        PosInTerm pit = PosInTerm.getTopLevel();

        pit = pit.down(8);
        assertEquals(8, pit.getIndex());
        assertEquals(1, pit.depth());


        PosInTerm copy = pit;

        pit = pit.down(20);
        assertEquals(2, pit.depth());
        assertEquals(20, pit.getIndex());


        assertNotEquals(pit, copy);
        assertEquals(8, copy.getIndex());
        assertEquals(1, copy.depth());

        pit = pit.up();
        assertEquals(copy, pit);

        pit = pit.up();
        pit = pit.down(15);
        assertEquals(8, copy.getIndex());
        assertEquals(15, pit.getIndex());
    }

    @Test
    public void testCopyFlag() {
        PosInTerm pit = PosInTerm.getTopLevel();
        pit = pit.down(10);

        PosInTerm copy = pit;
        pit = pit.down(20);
        copy = copy.down(30);

        assertEquals(20, pit.getIndex());
        assertEquals(30, copy.getIndex());
    }

    @Test
    public void testUpDownWithCopy() {
        int[] pos = new int[] { 10, 2, 5, 20, 4, 100, 25, 65, 23, 40, 2, 0, 1, 0, 1 };

        PosInTerm pit = toPosInTerm(pos);

        PosInTerm copy = pit;

        assertEquals(pos.length, pit.depth());

        for (int i = 0; i < pit.depth(); i++) {
            assertEquals(pos[i], pit.getIndexAt(i));
        }

        pit = pit.up().up().up();
        pit = pit.down(10000).down(1000);

        // old unchanged
        for (int i = 0; i < pit.depth(); i++) {
            assertEquals(copy.getIndexAt(i), pos[i],
                "PosInTerms should be immutable, but" + "an old one was changed");
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

    @Test
    public void testEquals() {
        int[] pos = new int[] { 10, 2, 5, 20, 4, 100, 25, 65, 23, 40, 2, 0, 1, 0, 1 };
        int[] pos2 = new int[] { 10, 2, 5, 20, 4, 100, 75, 65, 23, 40, 2, 0, 1, 0, 1 };
        int[] pos3 = new int[] { 10, 2, 5, 20, 4, 100, 25, 2, 0, 1, 0, 1 };
        int[] pos4 = new int[] { 10, 2, 5, 20, 4, 100, 25, 65, 23, 40, 2, 0, 1, 0, 1, 67, 68, 69 };


        PosInTerm pit1 = toPosInTerm(pos);
        PosInTerm pit2 = toPosInTerm(pos);
        assertEquals(pit1, pit2);
        assertEquals(pit1.hashCode(), pit2.hashCode());

        Assertions.assertNotEquals(pit1, toPosInTerm(pos2));
        Assertions.assertNotEquals(pit1, toPosInTerm(pos3));
        Assertions.assertNotEquals(pit1, toPosInTerm(pos4));
    }

    @Test
    public void testFirstN() {
        int[] pos = new int[] { 10, 2, 5, 20, 4, 100, 25, 65, 23, 40, 2, 0, 1, 0, 1 };
        int[] posN4 = new int[] { 10, 2, 5, 20 };
        int[] posN7 = new int[] { 10, 2, 5, 20, 4, 100, 25 };

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

    @Test
    public void testIntegerList() {
        int[] pos = new int[] { 10, 2, 5, 20, 4, 100, 25, 65, 23, 40, 2, 0, 1, 0, 1 };

        PosInTerm pit = toPosInTerm(pos);

        assertEquals("[10,2,5,20,4,100,25,65,23,40,2,0,1,0,1]", pit.integerList(pit.iterator()));
        assertEquals("[1,0,1,0,2,40,23,65,25,100,4,20,5,2,10]",
            pit.integerList(pit.reverseIterator()));
    }

    @Test
    public void testParseReverseString() {
        int[] pos = new int[] { 10, 2, 5, 20, 4, 100, 25, 65, 23, 40, 2, 0, 1, 0, 1 };

        PosInTerm pit = toPosInTerm(pos);

        assertEquals(pit, PosInTerm.parseReverseString("1,0,1,0,2,40,23,65,25,100,4,20,5,2,10"));

    }

}

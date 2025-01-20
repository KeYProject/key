/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.util.pp;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Unit-Test the {@link Layouter} class.
 */

public class TestLayouter {
    /**
     * A layouter which breaks everything
     */
    Layouter<Void> narrow;
    /**
     * A layouter which breaks nothing
     */
    Layouter<Void> wide;
    /**
     * A layouter which breaks nothing
     */
    Layouter<Void> six;
    /**
     * A layouter which breaks nothing
     */
    Layouter<Void> marking;

    int[] marks;
    int markPtr;

    @BeforeEach
    public void setUp() {
        narrow = new Layouter<>(new StringBackend<>(), 1, 2);
        wide = new Layouter<>(new StringBackend<>(), 10000, 2);
        six = new Layouter<>(new StringBackend<>(), 6, 2);
        marking = new Layouter<>(new MarkingBackend(), 1, 2);
        marks = new int[100];
        markPtr = 0;
    }


    class MarkingBackend extends StringBackend<Void> {
        @Override
        public void mark(Void o) {
            marks[markPtr++] = count();
        }
    }

    @Test
    public void testNarrowConsistent() throws UnbalancedBlocksException {
        narrow.beginC().print("A").beginC().print("B").brk(1, 2).print("C").brk(2, 3).print("D")
                .end().print("E").end().close();
        assertEquals("AB\n     C\n      DE", narrow.result(), "break consistent");
    }

    @Test
    public void testWideConsistent() throws UnbalancedBlocksException {
        wide.beginC().print("A").beginC().print("B").brk(1, 2).print("C").brk(2, 3).print("D").end()
                .print("E").end().close();
        assertEquals("AB C  DE", wide.result(), "no break consistent");
    }

    @Test
    public void testNarrowInconsistent() throws UnbalancedBlocksException {
        narrow.beginC().print("A").beginI().print("B").brk(1, 2).print("C").brk(2, 3).print("D")
                .end().print("E").end().close();
        assertEquals("AB\n     C\n      DE", narrow.result(), "break inconsistent");
    }

    @Test
    public void testWideInconsistent() throws UnbalancedBlocksException {
        wide.beginC().print("A").beginI().print("B").brk(1, 2).print("C").brk(2, 3).print("D").end()
                .print("E").end().close();
        assertEquals("AB C  DE", wide.result(), "no break inconsistent");
    }

    @Test
    public void testSixInconsistent() throws UnbalancedBlocksException {
        six.beginC().print("A").beginI().print("B").brk(1, 2).print("C").brk(2, 3).print("D").end()
                .print("E").end().close();
        assertEquals("AB C\n      DE", six.result(), "some breaks inconsistent");
    }

    @Test
    public void testNarrowPre() throws UnbalancedBlocksException {
        narrow.beginC().print("[").pre("A\nB\nC").print("]").end().close();
        assertEquals("[A\n B\n C]", narrow.result(), "preformatted");
    }

    @Test
    public void testWidePre() throws UnbalancedBlocksException {
        wide.beginC().print("[").pre("A\nB\nC").print("]").end().close();
        assertEquals("[A\n B\n C]", wide.result(), "preformatted");

    }

    @Test
    public void testNarrowInd() throws UnbalancedBlocksException {
        narrow.beginC().print("A").beginC().ind(1, 2).print("B").brk(1, 2).print("C").ind(3, 4)
                .print("D").brk(2, 3).print("E").end().print("F").end().close();
        assertEquals("A    B\n     C D\n      EF", narrow.result(), "ind consistent");
    }

    @Test
    public void testWideInd() throws UnbalancedBlocksException {
        wide.beginC().print("A").beginC().ind(1, 2).print("B").brk(1, 2).print("C").ind(3, 4)
                .print("D").brk(2, 3).print("E").end().print("F").end().close();
        assertEquals("A B C   D  EF", wide.result(), "ind consistent");
    }

    @Test
    public void testMark() throws UnbalancedBlocksException {
        marking.beginC().mark(null).print("A").mark(null).beginC().mark(null).print("B").mark(null)
                .brk(1, 2).mark(null).print("C").mark(null).brk(2, 3).mark(null).print("D")
                .mark(null).end().mark(null).print("E").mark(null).end().mark(null).close();
        assertEquals("AB\n     C\n      DE", marking.result(), "break consistent");
        assertEquals(11, markPtr, "number marks");
        assertEquals(0, marks[0], "marks pos 1");
        assertEquals(1, marks[1], "marks pos 2");
        assertEquals(1, marks[2], "marks pos 3");
        assertEquals(2, marks[3], "marks pos 4");
        assertEquals(8, marks[4], "marks pos 5");
        assertEquals(9, marks[5], "marks pos 6");
        assertEquals(16, marks[6], "marks pos 7");
        assertEquals(17, marks[7], "marks pos 8");
        assertEquals(17, marks[8], "marks pos 9");
        assertEquals(18, marks[9], "marks pos 10");
        assertEquals(18, marks[10], "marks pos 11");
    }
}

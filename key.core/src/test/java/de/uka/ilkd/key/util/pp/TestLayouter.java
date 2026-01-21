package de.uka.ilkd.key.util.pp;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.io.IOException;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Unit-Test the {@link Layouter} class.
 */

public class TestLayouter {

    /**
     * A backend to remember the result in
     */
    StringBackend narrowBack;
    /**
     * A backend to remember the result in
     */
    StringBackend wideBack;
    /**
     * A backend to remember the result in
     */
    StringBackend sixBack;
    /**
     * A layouter which breaks everything
     */
    MarkingBackend markBack;
    /**
     * A layouter which breaks everything
     */
    Layouter narrow;
    /**
     * A layouter which breaks nothing
     */
    Layouter wide;
    /**
     * A layouter which breaks nothing
     */
    Layouter six;
    /**
     * A layouter which breaks nothing
     */
    Layouter marking;

    int[] marks;
    int markPtr;

    @BeforeEach
    public void setUp() {
        narrowBack = new StringBackend(1);
        wideBack = new StringBackend(10000);
        sixBack = new StringBackend(6);
        markBack = new MarkingBackend(1);
        narrow = new Layouter(narrowBack, 2);
        wide = new Layouter(wideBack, 2);
        six = new Layouter(sixBack, 2);
        marking = new Layouter(markBack, 2);
        marks = new int[100];
        markPtr = 0;
    }


    class MarkingBackend extends StringBackend implements Backend {
        public MarkingBackend(int lineWidth) {
            super(lineWidth);
        }

        public void mark(Object o) {
            marks[markPtr++] = count();
        }
    }

    @Test
    public void testNarrowConsistent() throws UnbalancedBlocksException, IOException {
        narrow.beginC().print("A").beginC().print("B").brk(1, 2).print("C").brk(2, 3).print("D")
                .end().print("E").end().close();
        assertEquals("AB\n     C\n      DE", narrowBack.getString(), "break consistent");
    }

    @Test
    public void testWideConsistent() throws UnbalancedBlocksException, IOException {
        wide.beginC().print("A").beginC().print("B").brk(1, 2).print("C").brk(2, 3).print("D").end()
                .print("E").end().close();
        assertEquals("AB C  DE", wideBack.getString(), "no break consistent");
    }

    @Test
    public void testNarrowInconsistent() throws UnbalancedBlocksException, IOException {
        narrow.beginC().print("A").beginI().print("B").brk(1, 2).print("C").brk(2, 3).print("D")
                .end().print("E").end().close();
        assertEquals("AB\n     C\n      DE", narrowBack.getString(), "break inconsistent");
    }

    @Test
    public void testWideInconsistent() throws UnbalancedBlocksException, IOException {
        wide.beginC().print("A").beginI().print("B").brk(1, 2).print("C").brk(2, 3).print("D").end()
                .print("E").end().close();
        assertEquals("AB C  DE", wideBack.getString(), "no break inconsistent");
    }

    @Test
    public void testSixInconsistent() throws UnbalancedBlocksException, IOException {
        six.beginC().print("A").beginI().print("B").brk(1, 2).print("C").brk(2, 3).print("D").end()
                .print("E").end().close();
        assertEquals("AB C\n      DE", sixBack.getString(), "some breaks inconsistent");
    }

    @Test
    public void testNarrowPre() throws UnbalancedBlocksException, IOException {
        narrow.beginC().print("[").pre("A\nB\nC").print("]").end().close();
        assertEquals("[A\n B\n C]", narrowBack.getString(), "preformatted");

    }

    @Test
    public void testWidePre() throws UnbalancedBlocksException, IOException {
        wide.beginC().print("[").pre("A\nB\nC").print("]").end().close();
        assertEquals("[A\n B\n C]", wideBack.getString(), "preformatted");

    }

    @Test
    public void testNarrowInd() throws UnbalancedBlocksException, IOException {
        narrow.beginC().print("A").beginC().ind(1, 2).print("B").brk(1, 2).print("C").ind(3, 4)
                .print("D").brk(2, 3).print("E").end().print("F").end().close();
        assertEquals("A    B\n     C D\n      EF", narrowBack.getString(), "ind consistent");
    }

    @Test
    public void testWideInd() throws UnbalancedBlocksException, IOException {
        wide.beginC().print("A").beginC().ind(1, 2).print("B").brk(1, 2).print("C").ind(3, 4)
                .print("D").brk(2, 3).print("E").end().print("F").end().close();
        assertEquals("A B C   D  EF", wideBack.getString(), "ind consistent");
    }

    @Test
    public void testMark() throws UnbalancedBlocksException, IOException {
        marking.beginC().mark(null).print("A").mark(null).beginC().mark(null).print("B").mark(null)
                .brk(1, 2).mark(null).print("C").mark(null).brk(2, 3).mark(null).print("D")
                .mark(null).end().mark(null).print("E").mark(null).end().mark(null).close();
        assertEquals("AB\n     C\n      DE", markBack.getString(), "break consistent");
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

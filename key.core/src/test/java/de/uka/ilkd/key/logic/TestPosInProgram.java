/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic;

import java.util.Arrays;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.declaration.LocalVariableDeclaration;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.java.expression.literal.IntLiteral;
import de.uka.ilkd.key.java.reference.TypeRef;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.logic.sort.SortImpl;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.MethodSource;

import static org.junit.jupiter.api.Assertions.*;

class TestPosInProgram {


    static int[][] validPositions() {
        return new int[][] {
            {},
            { 0 },
            { 1 },
            { 0, 1 },
            { 1, 0, 2 },
            { 0, 2, 5, 3, 2, 1, 1, 1, 0, 1, 1, 2, 2, 3, 4 },
        };
    }

    static int[][] invalidPositions() {
        return new int[][] {
            { 3, -1 },
            { -4 },
            { 0, 3, -3, 7 }
        };
    }

    @Test
    void getProgramAt() {
    }

    @ParameterizedTest(name = "{index}: ==> (0)")
    @MethodSource("validPositions")
    void depth(int[] pos) {
        PosInProgram pip = PosInProgram.TOP;
        assertEquals(0, pip.depth(), "Wrong top position");
        for (int po : pos) {
            pip = pip.down(po);
        }
        assertEquals(pos.length, pip.depth(), "Wrong position depth for " + Arrays.toString(pos));
    }

    @ParameterizedTest(name = "{index}: ==> (0)")
    @MethodSource("validPositions")
    void downValid(int[] pos) {
        PosInProgram pip = getPiPFor(pos);

        for (int i = 0; i < pip.depth(); i++) {
            assertEquals(pos[i], pip.get(i), "Wrong position for " + Arrays.toString(pos));
        }
    }

    private static PosInProgram getPiPFor(int[] pos) {
        PosInProgram pip = PosInProgram.TOP;
        for (int po : pos) {
            pip = pip.down(po);
        }
        return pip;
    }

    @ParameterizedTest(name = "{index}: ==> (0)")
    @MethodSource("invalidPositions")
    void downInvalid(int[] pos) {
        // Should pass also for invalid positions as positions not verified during construction
        // by intent; error thrown when querying position in a program
        PosInProgram pip = getPiPFor(pos);

        for (int i = 0; i < pip.depth(); i++) {
            assertEquals(pos[i], pip.get(i), "Wrong position for " + Arrays.toString(pos));
        }
    }

    @ParameterizedTest(name = "{index}: ==> (0)")
    @MethodSource("validPositions")
    void up(int[] pos) {
        PosInProgram pip = PosInProgram.TOP;
        for (int po : pos) {
            PosInProgram pipTmp = pip.down(po);
            assertEquals(pip, pipTmp.up());
            pip = pipTmp;
        }

        for (int i = pip.depth() - 1; i >= 0; i--) {
            int lastPos = pip.last();
            pip = pip.up();
            assertEquals(pos[i], lastPos, "Wrong position for " + Arrays.toString(pos));
        }

        assertSame(PosInProgram.TOP, pip, "Top position should have been reached");
    }

    @Test
    void append() {
        final PosInProgram pip4 = getPiPFor(validPositions()[4]);
        final PosInProgram pip5 = getPiPFor(validPositions()[5]);

        assertSame(PosInProgram.TOP, PosInProgram.TOP.append(PosInProgram.TOP));
        assertEquals(pip4, pip4.append(PosInProgram.TOP));
        assertEquals(pip4, PosInProgram.TOP.append(pip4));

        final PosInProgram both = pip4.append(pip5);
        for (int i = 0; i < pip4.depth(); i++) {
            assertEquals(validPositions()[4][i], both.get(i));
        }
        for (int i = 0; i < pip5.depth(); i++) {
            assertEquals(validPositions()[5][i], both.get(i + pip4.depth()));
        }
    }

    @Test
    void prepend() {
        final PosInProgram pip4 = getPiPFor(validPositions()[4]);
        final PosInProgram pip5 = getPiPFor(validPositions()[5]);

        assertSame(PosInProgram.TOP, PosInProgram.TOP.prepend(PosInProgram.TOP));
        assertEquals(pip4, pip4.prepend(PosInProgram.TOP));
        assertEquals(pip4, PosInProgram.TOP.prepend(pip4));

        final PosInProgram both = pip4.prepend(pip5);
        assertEquals(pip4.depth() + pip5.depth(), both.depth(), "Depth mismatch");
        for (int i = 0; i < pip5.depth(); i++) {
            assertEquals(validPositions()[5][i], both.get(i),
                "Invalid content at index " + i + ":" + both);
        }
        for (int i = 0; i < pip4.depth(); i++) {
            assertEquals(validPositions()[4][i], both.get(i + pip5.depth()));
        }
        assertEquals(both, pip5.append(pip4));
    }

    @Test
    void testEquals() {
        final PosInProgram pip4a = getPiPFor(validPositions()[4]);
        final PosInProgram pip4b = getPiPFor(validPositions()[4]);
        assertEquals(pip4a, pip4b);

        final PosInProgram pip5 = getPiPFor(validPositions()[5]);
        assertNotEquals(pip4a, pip5);


        // same length first element different
        assertNotEquals(
            getPiPFor(new int[] { 0, 2, 5, 3, 2, 1, 1, 1, 0, 1, 1, 2, 2, 3, 7 }),
            getPiPFor(new int[] { 1, 2, 5, 3, 2, 1, 1, 1, 0, 1, 1, 2, 2, 3, 7 }));

        // same length element in middle different
        assertNotEquals(
            getPiPFor(new int[] { 0, 2, 5, 3, 2, 1, 1, 1, 0, 1, 1, 2, 2, 3, 7 }),
            getPiPFor(new int[] { 0, 2, 5, 3, 2, 1, 1, 8, 0, 1, 1, 2, 2, 3, 7 }));

        // same length last element different
        assertNotEquals(
            getPiPFor(new int[] { 0, 2, 5, 3, 2, 1, 1, 1, 0, 1, 1, 2, 2, 3, 7 }),
            getPiPFor(new int[] { 0, 2, 5, 3, 2, 1, 1, 1, 0, 1, 1, 2, 2, 3, 8 }));

        // equals for TOP
        assertEquals(PosInProgram.TOP, PosInProgram.TOP);
        assertNotEquals(PosInProgram.TOP,
            getPiPFor(new int[] { 0, 2, 5, 3, 2, 1, 1, 1, 0, 1, 1, 2, 2, 3, 7 }));
    }

    @Test
    void leq() {
        assertTrue(
            PosInProgram.TOP.leq(
                getPiPFor(new int[] { 0, 2, 5, 3, 2, 1, 1, 1, 0, 1, 1, 2, 2, 3, 8 })));

        assertFalse(getPiPFor(new int[] { 0, 2, 5, 3, 2, 1, 1, 1, 0, 1, 1, 2, 2, 3, 8 })
                .leq(PosInProgram.TOP));

        assertTrue(
            getPiPFor(new int[] { 0, 2, 5, 3, 2, 1, 1, 1, 0, 1, 1, 2, 2, 3 }).leq(
                getPiPFor(new int[] { 0, 2, 5, 3, 2, 1, 1, 1, 0, 1, 1, 2, 2, 3, 8 })));

        assertFalse(
            getPiPFor(new int[] { 0, 2, 5, 3, 2, 1, 1, 1, 0, 1, 1, 2, 2, 3, 8 }).leq(
                getPiPFor(new int[] { 0, 2, 5, 3, 2, 1, 1, 1, 0, 1, 1, 2, 2, 3 })));

    }

    @Test
    void getInsindeBounds() {
        final PosInProgram pip5 = getPiPFor(validPositions()[5]);
        for (int i = 0; i < pip5.depth(); i++) {
            assertEquals(validPositions()[5][i], pip5.get(i));
        }
    }

    @Test
    void getOutsideBounds() {
        final PosInProgram pip5 = getPiPFor(validPositions()[5]);
        assertThrows(IndexOutOfBoundsException.class,
            () -> pip5.get(pip5.depth()));
    }


    @Test
    void last() {
        final PosInProgram pip5 = getPiPFor(validPositions()[5]);
        assertEquals(validPositions()[5][validPositions()[5].length - 1], pip5.last());
    }

    @Test
    void getProgram() {
        Sort byteS = new SortImpl(new Name("byte"));
        LocationVariable var = new LocationVariable(new ProgramElementName("j"), byteS);
        KeYJavaType kjt = new KeYJavaType(PrimitiveType.JAVA_BYTE, byteS);
        TypeRef typeRef = new TypeRef(kjt);
        VariableSpecification spec = new VariableSpecification(var, new IntLiteral(0), kjt);
        LocalVariableDeclaration lvd = new LocalVariableDeclaration(typeRef, spec);

        assertSame(lvd, PosInProgram.getProgramAt(PosInProgram.TOP, lvd));
        assertSame(typeRef, PosInProgram.getProgramAt(PosInProgram.ZERO, lvd));
        assertSame(spec, PosInProgram.getProgramAt(PosInProgram.ONE, lvd));
        assertSame(var, PosInProgram.getProgramAt(PosInProgram.ONE_ZERO, lvd));
    }

    @Test
    void iterator() {
        final PosInProgram pip5 = getPiPFor(validPositions()[5]);
        var it = pip5.iterator();
        for (int i = 0; it.hasNext(); i++) {
            assertEquals(validPositions()[5][i], it.next(), "Wrong content at index" + i);
        }
        assertFalse(it.hasNext(), "Iterator has still elements.");
    }
}

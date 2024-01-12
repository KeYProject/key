/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.symbolic_execution.testcase;

import de.uka.ilkd.key.symbolic_execution.TruthValueTracingUtil.TruthValue;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;


/**
 * Tests for {@link TruthValue}.
 *
 * @author Martin Hentschel
 */
public class TestTruthValueValue {
    /**
     * Tests {@link TruthValue#ifThenElse(TruthValue, TruthValue, TruthValue)}.
     */
    @Test
    public void testIfThenElse() {
        // true
        assertEquals(TruthValue.TRUE,
            TruthValue.ifThenElse(TruthValue.TRUE, TruthValue.TRUE, TruthValue.TRUE));
        assertEquals(TruthValue.TRUE,
            TruthValue.ifThenElse(TruthValue.TRUE, TruthValue.TRUE, TruthValue.FALSE));
        assertEquals(TruthValue.TRUE,
            TruthValue.ifThenElse(TruthValue.TRUE, TruthValue.TRUE, TruthValue.UNKNOWN));
        assertEquals(TruthValue.TRUE,
            TruthValue.ifThenElse(TruthValue.TRUE, TruthValue.TRUE, null));
        assertEquals(TruthValue.FALSE,
            TruthValue.ifThenElse(TruthValue.TRUE, TruthValue.FALSE, TruthValue.TRUE));
        assertEquals(TruthValue.FALSE,
            TruthValue.ifThenElse(TruthValue.TRUE, TruthValue.FALSE, TruthValue.FALSE));
        assertEquals(TruthValue.FALSE,
            TruthValue.ifThenElse(TruthValue.TRUE, TruthValue.FALSE, TruthValue.UNKNOWN));
        assertEquals(TruthValue.FALSE,
            TruthValue.ifThenElse(TruthValue.TRUE, TruthValue.FALSE, null));
        assertEquals(TruthValue.UNKNOWN,
            TruthValue.ifThenElse(TruthValue.TRUE, TruthValue.UNKNOWN, TruthValue.TRUE));
        assertEquals(TruthValue.UNKNOWN,
            TruthValue.ifThenElse(TruthValue.TRUE, TruthValue.UNKNOWN, TruthValue.FALSE));
        assertEquals(TruthValue.UNKNOWN,
            TruthValue.ifThenElse(TruthValue.TRUE, TruthValue.UNKNOWN, TruthValue.UNKNOWN));
        assertEquals(TruthValue.UNKNOWN,
            TruthValue.ifThenElse(TruthValue.TRUE, TruthValue.UNKNOWN, null));
        assertNull(TruthValue.ifThenElse(TruthValue.TRUE, null, TruthValue.TRUE));
        assertNull(TruthValue.ifThenElse(TruthValue.TRUE, null, TruthValue.FALSE));
        assertNull(TruthValue.ifThenElse(TruthValue.TRUE, null, TruthValue.UNKNOWN));
        assertNull(TruthValue.ifThenElse(TruthValue.TRUE, null, null));
        // false
        assertEquals(TruthValue.TRUE,
            TruthValue.ifThenElse(TruthValue.FALSE, TruthValue.TRUE, TruthValue.TRUE));
        assertEquals(TruthValue.FALSE,
            TruthValue.ifThenElse(TruthValue.FALSE, TruthValue.TRUE, TruthValue.FALSE));
        assertEquals(TruthValue.UNKNOWN,
            TruthValue.ifThenElse(TruthValue.FALSE, TruthValue.TRUE, TruthValue.UNKNOWN));
        assertNull(TruthValue.ifThenElse(TruthValue.FALSE, TruthValue.TRUE, null));
        assertEquals(TruthValue.TRUE,
            TruthValue.ifThenElse(TruthValue.FALSE, TruthValue.FALSE, TruthValue.TRUE));
        assertEquals(TruthValue.FALSE,
            TruthValue.ifThenElse(TruthValue.FALSE, TruthValue.FALSE, TruthValue.FALSE));
        assertEquals(TruthValue.UNKNOWN,
            TruthValue.ifThenElse(TruthValue.FALSE, TruthValue.FALSE, TruthValue.UNKNOWN));
        assertNull(TruthValue.ifThenElse(TruthValue.FALSE, TruthValue.FALSE, null));
        assertEquals(TruthValue.TRUE,
            TruthValue.ifThenElse(TruthValue.FALSE, TruthValue.UNKNOWN, TruthValue.TRUE));
        assertEquals(TruthValue.FALSE,
            TruthValue.ifThenElse(TruthValue.FALSE, TruthValue.UNKNOWN, TruthValue.FALSE));
        assertEquals(TruthValue.UNKNOWN,
            TruthValue.ifThenElse(TruthValue.FALSE, TruthValue.UNKNOWN, TruthValue.UNKNOWN));
        assertNull(TruthValue.ifThenElse(TruthValue.FALSE, TruthValue.UNKNOWN, null));
        assertEquals(TruthValue.TRUE,
            TruthValue.ifThenElse(TruthValue.FALSE, null, TruthValue.TRUE));
        assertEquals(TruthValue.FALSE,
            TruthValue.ifThenElse(TruthValue.FALSE, null, TruthValue.FALSE));
        assertEquals(TruthValue.UNKNOWN,
            TruthValue.ifThenElse(TruthValue.FALSE, null, TruthValue.UNKNOWN));
        assertNull(TruthValue.ifThenElse(TruthValue.FALSE, null, null));
        // unknown
        assertEquals(TruthValue.UNKNOWN,
            TruthValue.ifThenElse(TruthValue.UNKNOWN, TruthValue.TRUE, TruthValue.TRUE));
        assertEquals(TruthValue.UNKNOWN,
            TruthValue.ifThenElse(TruthValue.UNKNOWN, TruthValue.TRUE, TruthValue.FALSE));
        assertEquals(TruthValue.UNKNOWN,
            TruthValue.ifThenElse(TruthValue.UNKNOWN, TruthValue.TRUE, TruthValue.UNKNOWN));
        assertEquals(TruthValue.UNKNOWN,
            TruthValue.ifThenElse(TruthValue.UNKNOWN, TruthValue.TRUE, null));
        assertEquals(TruthValue.UNKNOWN,
            TruthValue.ifThenElse(TruthValue.UNKNOWN, TruthValue.FALSE, TruthValue.TRUE));
        assertEquals(TruthValue.UNKNOWN,
            TruthValue.ifThenElse(TruthValue.UNKNOWN, TruthValue.FALSE, TruthValue.FALSE));
        assertEquals(TruthValue.UNKNOWN,
            TruthValue.ifThenElse(TruthValue.UNKNOWN, TruthValue.FALSE, TruthValue.UNKNOWN));
        assertEquals(TruthValue.UNKNOWN,
            TruthValue.ifThenElse(TruthValue.UNKNOWN, TruthValue.FALSE, null));
        assertEquals(TruthValue.UNKNOWN,
            TruthValue.ifThenElse(TruthValue.UNKNOWN, TruthValue.UNKNOWN, TruthValue.TRUE));
        assertEquals(TruthValue.UNKNOWN,
            TruthValue.ifThenElse(TruthValue.UNKNOWN, TruthValue.UNKNOWN, TruthValue.FALSE));
        assertEquals(TruthValue.UNKNOWN,
            TruthValue.ifThenElse(TruthValue.UNKNOWN, TruthValue.UNKNOWN, TruthValue.UNKNOWN));
        assertEquals(TruthValue.UNKNOWN,
            TruthValue.ifThenElse(TruthValue.UNKNOWN, TruthValue.UNKNOWN, null));
        assertEquals(TruthValue.UNKNOWN,
            TruthValue.ifThenElse(TruthValue.UNKNOWN, null, TruthValue.TRUE));
        assertEquals(TruthValue.UNKNOWN,
            TruthValue.ifThenElse(TruthValue.UNKNOWN, null, TruthValue.FALSE));
        assertEquals(TruthValue.UNKNOWN,
            TruthValue.ifThenElse(TruthValue.UNKNOWN, null, TruthValue.UNKNOWN));
        assertEquals(TruthValue.UNKNOWN, TruthValue.ifThenElse(TruthValue.UNKNOWN, null, null));
        // null
        assertEquals(TruthValue.UNKNOWN,
            TruthValue.ifThenElse(null, TruthValue.TRUE, TruthValue.TRUE));
        assertEquals(TruthValue.UNKNOWN,
            TruthValue.ifThenElse(null, TruthValue.TRUE, TruthValue.FALSE));
        assertEquals(TruthValue.UNKNOWN,
            TruthValue.ifThenElse(null, TruthValue.TRUE, TruthValue.UNKNOWN));
        assertEquals(TruthValue.UNKNOWN, TruthValue.ifThenElse(null, TruthValue.TRUE, null));
        assertEquals(TruthValue.UNKNOWN,
            TruthValue.ifThenElse(null, TruthValue.FALSE, TruthValue.TRUE));
        assertEquals(TruthValue.UNKNOWN,
            TruthValue.ifThenElse(null, TruthValue.FALSE, TruthValue.FALSE));
        assertEquals(TruthValue.UNKNOWN,
            TruthValue.ifThenElse(null, TruthValue.FALSE, TruthValue.UNKNOWN));
        assertEquals(TruthValue.UNKNOWN, TruthValue.ifThenElse(null, TruthValue.FALSE, null));
        assertEquals(TruthValue.UNKNOWN,
            TruthValue.ifThenElse(null, TruthValue.UNKNOWN, TruthValue.TRUE));
        assertEquals(TruthValue.UNKNOWN,
            TruthValue.ifThenElse(null, TruthValue.UNKNOWN, TruthValue.FALSE));
        assertEquals(TruthValue.UNKNOWN,
            TruthValue.ifThenElse(null, TruthValue.UNKNOWN, TruthValue.UNKNOWN));
        assertEquals(TruthValue.UNKNOWN, TruthValue.ifThenElse(null, TruthValue.UNKNOWN, null));
        assertEquals(TruthValue.UNKNOWN, TruthValue.ifThenElse(null, null, TruthValue.TRUE));
        assertEquals(TruthValue.UNKNOWN, TruthValue.ifThenElse(null, null, TruthValue.FALSE));
        assertEquals(TruthValue.UNKNOWN, TruthValue.ifThenElse(null, null, TruthValue.UNKNOWN));
        assertEquals(TruthValue.UNKNOWN, TruthValue.ifThenElse(null, null, null));
    }

    /**
     * Tests {@link TruthValue#eqv(TruthValue, TruthValue)}.
     */
    @Test
    public void testEqv() {
        // true
        assertEquals(TruthValue.TRUE, TruthValue.eqv(TruthValue.TRUE, TruthValue.TRUE));
        assertEquals(TruthValue.FALSE, TruthValue.eqv(TruthValue.TRUE, TruthValue.FALSE));
        assertEquals(TruthValue.UNKNOWN, TruthValue.eqv(TruthValue.TRUE, TruthValue.UNKNOWN));
        assertEquals(TruthValue.UNKNOWN, TruthValue.eqv(TruthValue.TRUE, null));
        // false
        assertEquals(TruthValue.FALSE, TruthValue.eqv(TruthValue.FALSE, TruthValue.TRUE));
        assertEquals(TruthValue.TRUE, TruthValue.eqv(TruthValue.FALSE, TruthValue.FALSE));
        assertEquals(TruthValue.UNKNOWN, TruthValue.eqv(TruthValue.FALSE, TruthValue.UNKNOWN));
        assertEquals(TruthValue.UNKNOWN, TruthValue.eqv(TruthValue.FALSE, null));
        // unknown
        assertEquals(TruthValue.UNKNOWN, TruthValue.eqv(TruthValue.UNKNOWN, TruthValue.TRUE));
        assertEquals(TruthValue.UNKNOWN, TruthValue.eqv(TruthValue.UNKNOWN, TruthValue.FALSE));
        assertEquals(TruthValue.UNKNOWN, TruthValue.eqv(TruthValue.UNKNOWN, TruthValue.UNKNOWN));
        assertEquals(TruthValue.UNKNOWN, TruthValue.eqv(TruthValue.UNKNOWN, null));
        // null
        assertEquals(TruthValue.UNKNOWN, TruthValue.eqv(null, TruthValue.TRUE));
        assertEquals(TruthValue.UNKNOWN, TruthValue.eqv(null, TruthValue.FALSE));
        assertEquals(TruthValue.UNKNOWN, TruthValue.eqv(null, TruthValue.UNKNOWN));
        assertEquals(TruthValue.UNKNOWN, TruthValue.eqv(null, null));
    }

    /**
     * Tests {@link TruthValue#and(TruthValue, TruthValue)}.
     */
    @Test
    public void testAnd() {
        // true
        assertEquals(TruthValue.TRUE, TruthValue.and(TruthValue.TRUE, TruthValue.TRUE));
        assertEquals(TruthValue.FALSE, TruthValue.and(TruthValue.TRUE, TruthValue.FALSE));
        assertEquals(TruthValue.UNKNOWN, TruthValue.and(TruthValue.TRUE, TruthValue.UNKNOWN));
        assertEquals(TruthValue.UNKNOWN, TruthValue.and(TruthValue.TRUE, null));
        // false
        assertEquals(TruthValue.FALSE, TruthValue.and(TruthValue.FALSE, TruthValue.TRUE));
        assertEquals(TruthValue.FALSE, TruthValue.and(TruthValue.FALSE, TruthValue.FALSE));
        assertEquals(TruthValue.FALSE, TruthValue.and(TruthValue.FALSE, TruthValue.UNKNOWN));
        assertEquals(TruthValue.FALSE, TruthValue.and(TruthValue.FALSE, null));
        // unknown
        assertEquals(TruthValue.UNKNOWN, TruthValue.and(TruthValue.UNKNOWN, TruthValue.TRUE));
        assertEquals(TruthValue.FALSE, TruthValue.and(TruthValue.UNKNOWN, TruthValue.FALSE));
        assertEquals(TruthValue.UNKNOWN, TruthValue.and(TruthValue.UNKNOWN, TruthValue.UNKNOWN));
        assertEquals(TruthValue.UNKNOWN, TruthValue.and(TruthValue.UNKNOWN, null));
        // null
        assertEquals(TruthValue.UNKNOWN, TruthValue.and(null, TruthValue.TRUE));
        assertEquals(TruthValue.FALSE, TruthValue.and(null, TruthValue.FALSE));
        assertEquals(TruthValue.UNKNOWN, TruthValue.and(null, TruthValue.UNKNOWN));
        assertEquals(TruthValue.UNKNOWN, TruthValue.and(null, null));
    }

    /**
     * Tests {@link TruthValue#or(TruthValue, TruthValue)}.
     */
    @Test
    public void testOr() {
        // true
        assertEquals(TruthValue.TRUE, TruthValue.or(TruthValue.TRUE, TruthValue.TRUE));
        assertEquals(TruthValue.TRUE, TruthValue.or(TruthValue.TRUE, TruthValue.FALSE));
        assertEquals(TruthValue.TRUE, TruthValue.or(TruthValue.TRUE, TruthValue.UNKNOWN));
        assertEquals(TruthValue.TRUE, TruthValue.or(TruthValue.TRUE, null));
        // false
        assertEquals(TruthValue.TRUE, TruthValue.or(TruthValue.FALSE, TruthValue.TRUE));
        assertEquals(TruthValue.FALSE, TruthValue.or(TruthValue.FALSE, TruthValue.FALSE));
        assertEquals(TruthValue.UNKNOWN, TruthValue.or(TruthValue.FALSE, TruthValue.UNKNOWN));
        assertEquals(TruthValue.UNKNOWN, TruthValue.or(TruthValue.FALSE, null));
        // unknown
        assertEquals(TruthValue.TRUE, TruthValue.or(TruthValue.UNKNOWN, TruthValue.TRUE));
        assertEquals(TruthValue.UNKNOWN, TruthValue.or(TruthValue.UNKNOWN, TruthValue.FALSE));
        assertEquals(TruthValue.UNKNOWN, TruthValue.or(TruthValue.UNKNOWN, TruthValue.UNKNOWN));
        assertEquals(TruthValue.UNKNOWN, TruthValue.or(TruthValue.UNKNOWN, null));
        // null
        assertEquals(TruthValue.TRUE, TruthValue.or(null, TruthValue.TRUE));
        assertEquals(TruthValue.UNKNOWN, TruthValue.or(null, TruthValue.FALSE));
        assertEquals(TruthValue.UNKNOWN, TruthValue.or(null, TruthValue.UNKNOWN));
        assertEquals(TruthValue.UNKNOWN, TruthValue.or(null, null));
    }

    /**
     * Tests {@link TruthValue#imp(TruthValue, TruthValue)}.
     */
    @Test
    public void testImp() {
        // true
        assertEquals(TruthValue.TRUE, TruthValue.imp(TruthValue.TRUE, TruthValue.TRUE));
        assertEquals(TruthValue.FALSE, TruthValue.imp(TruthValue.TRUE, TruthValue.FALSE));
        assertEquals(TruthValue.UNKNOWN, TruthValue.imp(TruthValue.TRUE, TruthValue.UNKNOWN));
        assertEquals(TruthValue.UNKNOWN, TruthValue.imp(TruthValue.TRUE, null));
        // false
        assertEquals(TruthValue.TRUE, TruthValue.imp(TruthValue.FALSE, TruthValue.TRUE));
        assertEquals(TruthValue.TRUE, TruthValue.imp(TruthValue.FALSE, TruthValue.FALSE));
        assertEquals(TruthValue.TRUE, TruthValue.imp(TruthValue.FALSE, TruthValue.UNKNOWN));
        assertEquals(TruthValue.TRUE, TruthValue.imp(TruthValue.FALSE, null));
        // unknown
        assertEquals(TruthValue.TRUE, TruthValue.imp(TruthValue.UNKNOWN, TruthValue.TRUE));
        assertEquals(TruthValue.UNKNOWN, TruthValue.imp(TruthValue.UNKNOWN, TruthValue.FALSE));
        assertEquals(TruthValue.UNKNOWN, TruthValue.imp(TruthValue.UNKNOWN, TruthValue.UNKNOWN));
        assertEquals(TruthValue.UNKNOWN, TruthValue.imp(TruthValue.UNKNOWN, null));
        // null
        assertEquals(TruthValue.TRUE, TruthValue.imp(null, TruthValue.TRUE));
        assertEquals(TruthValue.UNKNOWN, TruthValue.imp(null, TruthValue.FALSE));
        assertEquals(TruthValue.UNKNOWN, TruthValue.imp(null, TruthValue.UNKNOWN));
        assertEquals(TruthValue.UNKNOWN, TruthValue.imp(null, null));
    }

    /**
     * Tests {@link TruthValue#not(TruthValue)}.
     */
    @Test
    public void testNot() {
        assertEquals(TruthValue.FALSE, TruthValue.not(TruthValue.TRUE));
        assertEquals(TruthValue.TRUE, TruthValue.not(TruthValue.FALSE));
        assertEquals(TruthValue.UNKNOWN, TruthValue.not(TruthValue.UNKNOWN));
        assertEquals(TruthValue.UNKNOWN, TruthValue.not(null));
    }
}

/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.util;

import java.util.NoSuchElementException;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

class UnionTest {

    @Test
    void fromFirst() {
        Union<Integer, String> union = Union.fromFirst(42);
        assertTrue(union.isFirst());
        assertFalse(union.isSecond());
        assertEquals(42, union.getFirst());
        try {
            union.getSecond();
            fail("should have thrown exception");
        } catch (NoSuchElementException ex) {
            // expected
        }
    }

    @Test
    void fromSecond() {
        Union<Integer, String> union = Union.fromSecond("Hello World");
        assertTrue(union.isSecond());
        assertFalse(union.isFirst());
        assertEquals("Hello World", union.getSecond());
        try {
            union.getFirst();
            fail("should have thrown exception");
        } catch (NoSuchElementException ex) {
            // expected
        }
    }

    @Test
    void mapFirstOnFirst() {
        Union<Integer, String> union = Union.fromFirst(42);
        Union<Double, String> mapped = union.mapFirst(it -> it + 0.5);
        assertTrue(mapped.isFirst());
        assertFalse(mapped.isSecond());
        assertEquals(42.5, mapped.getFirst());
        try {
            mapped.getSecond();
            fail("should have thrown exception");
        } catch (NoSuchElementException ex) {
            // expected
        }
    }

    @Test
    void mapSecondOnFirst() {
        Union<Integer, String> union = Union.fromFirst(42);
        Union<Integer, Integer> mapped = union.mapSecond(String::length);
        assertTrue(mapped.isFirst());
        assertFalse(mapped.isSecond());
        assertEquals(42, mapped.getFirst());
        try {
            mapped.getSecond();
            fail("should have thrown exception");
        } catch (NoSuchElementException ex) {
            // expected
        }
    }

    @Test
    void mapFirstOnSecond() {
        Union<Integer, String> union = Union.fromSecond("Hello World");
        Union<Double, String> mapped = union.mapFirst(it -> it + 0.5);
        assertTrue(mapped.isSecond());
        assertFalse(mapped.isFirst());
        assertEquals("Hello World", mapped.getSecond());
        try {
            mapped.getFirst();
            fail("should have thrown exception");
        } catch (NoSuchElementException ex) {
            // expected
        }
    }

    @Test
    void mapSecondOnSecond() {
        Union<Integer, String> union = Union.fromSecond("Hello World");
        Union<Integer, Integer> mapped = union.mapSecond(String::length);
        assertTrue(mapped.isSecond());
        assertFalse(mapped.isFirst());
        assertEquals(11, mapped.getSecond());
        try {
            mapped.getFirst();
            fail("should have thrown exception");
        } catch (NoSuchElementException ex) {
            // expected
        }
    }

    @Test
    void testToString() {
        Union<Integer, String> union = Union.fromSecond("Hello World");
        assertEquals("Union{second alternative, value=Hello World}", union.toString());

        union = Union.fromFirst(42);
        assertEquals("Union{first alternative, value=42}", union.toString());
    }
}

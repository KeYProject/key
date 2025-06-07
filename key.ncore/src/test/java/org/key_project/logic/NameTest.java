/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.logic;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

class NameTest {

    final String[] names = { "", "a", "1a", "AB_3$3", " ghIK", ":", ":a", "#1" };

    @Test
    void testToString() {
        for (var s : names) {
            assertEquals(s, new Name(s).toString());
        }
    }

    @Test
    void testInternalized() {
        for (var s : names) {
            final Name n1 = new Name(s);
            final Name n2 = new Name(s);
            assertSame(n1.toString(), n2.toString());
        }
    }

    @Test
    void testEquals() {
        for (int i = 0; i < names.length; i++) {
            for (int j = 0; j < names.length; j++) {
                final Name n1 = new Name(names[i]);
                final Name n2 = new Name(names[j]);
                if (n1.equals(n2)) {
                    assertEquals(i, j);
                } else {
                    assertNotEquals(i, j);
                }
            }
        }
    }

    @Test
    void testEqualsWithNull() {
        assertNotEquals(null, new Name("a"));
    }

    @Test
    void compareTo() {
        assertTrue(new Name("a").compareTo(new Name("b")) < 0);
        assertTrue(new Name("A").compareTo(new Name("a")) < 0);
        assertTrue(new Name("a").compareTo(new Name("abc")) < 0);
        assertTrue(new Name("").compareTo(new Name("b")) < 0);
        assertEquals(0, new Name("").compareTo(new Name("")));
        assertEquals(0, new Name("a").compareTo(new Name("a")));
        assertTrue(new Name("b").compareTo(new Name("a")) > 0);
        assertTrue(new Name("a").compareTo(new Name("A")) > 0);
        assertTrue(new Name("abc").compareTo(new Name("")) > 0);
    }

    @Test
    void testHashCode() {
        for (String s : names) {
            for (String name : names) {
                final Name n1 = new Name(s);
                final Name n2 = new Name(name);
                if (n1.equals(n2)) {
                    assertEquals(n1.hashCode(), n2.hashCode(),
                        "Equal names must have equal hashes.");
                } else {
                    assertNotEquals(n1.hashCode(), n2.hashCode(),
                        "Hash Code function is not wrong, " +
                            "but most likely not sufficiently good.");
                }
            }
        }
    }
}

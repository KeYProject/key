/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.util;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;

public class TestLexicographicComparator {


    @Test
    public void testCompareInt() {
        Integer[] a = { 3, 4 };
        Integer[] b = { 1, 7 };
        final LexicographicComparator<Integer> lcc = new LexicographicComparator<>();
        assertEquals(-1, lcc.compare(a, b));
        b = new Integer[] { 3, 4, 0 };
        assertEquals(1, lcc.compare(a, b));
        a = new Integer[] { 3, 4, 0 };
        assertEquals(0, lcc.compare(a, b));
    }
}

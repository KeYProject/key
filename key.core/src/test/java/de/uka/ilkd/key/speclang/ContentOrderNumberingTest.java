/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang;

import java.util.List;
import java.util.function.Function;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;

class ContentOrderNumberingTest {

    private static final Function<String, String> IDENTITY = s -> s;

    /** The number of a member does not depend on the group's iteration order. */
    @Test
    void orderIndependent() {
        var forward = new ContentOrderNumbering<>(List.of("bb", "aa", "cc"), IDENTITY);
        var shuffled = new ContentOrderNumbering<>(List.of("cc", "aa", "bb"), IDENTITY);
        for (String member : List.of("aa", "bb", "cc")) {
            assertEquals(forward.numberOf(member), shuffled.numberOf(member),
                "number of '" + member + "' must not depend on input order");
        }
    }

    /** Distinct contents get distinct, gap-free numbers in content order. */
    @Test
    void distinctContentsGetGapFreeNumbers() {
        var n = new ContentOrderNumbering<>(List.of("cc", "aa", "bb"), IDENTITY);
        assertEquals(0, n.numberOf("aa"));
        assertEquals(1, n.numberOf("bb"));
        assertEquals(2, n.numberOf("cc"));
    }

    /**
     * Equal content keys share a number; different ones do not (collision-free by construction).
     */
    @Test
    void equalContentSharesNumberDifferentDoesNot() {
        var n = new ContentOrderNumbering<>(List.of("x", "x", "y"), IDENTITY);
        assertEquals(n.numberOf("x"), n.numberOf("x"));
        assertNotEquals(n.numberOf("x"), n.numberOf("y"));
    }
}

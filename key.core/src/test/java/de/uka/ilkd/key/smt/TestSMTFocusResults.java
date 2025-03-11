/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.smt;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;

/**
 * Tests for {@link SMTFocusResults}.
 */
class TestSMTFocusResults {
    @Test
    void parsesZ3Format() {
        String z3Output = "(L_1 L_17 L_23)";
        Integer[] result = SMTFocusResults.parseZ3Format(z3Output);
        Assertions.assertArrayEquals(new Integer[] { 1, 17, 23 }, result);
    }

    @Test
    void parsesCvc5Format() {
        String[] cvc5Output = new String[] {
            "(",
            "L_5",
            "L_12",
            "L_23",
            ")"
        };
        Integer[] result = SMTFocusResults.parseCVC5Format(cvc5Output);
        Assertions.assertArrayEquals(new Integer[] { 5, 12, 23 }, result);
    }
}

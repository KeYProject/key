/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.nparser;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.RealLDT;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.rule.TacletForTests;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Tests around issue #3570: real number literals such as {@code 1.0r} can be parsed into a term of
 * sort {@code real} (encoded as {@code __R(unscaledValue, scale)}) and printed back to their
 * decimal form.
 */
class Issue3570Test {

    private static KeyIO io() {
        Services services = TacletForTests.services().copy(false);
        return new KeyIO(services, services.getNamespaces());
    }

    @Test
    void realLiteralParsesToRealSort() {
        JTerm t = io().parseExpression("1.25r");
        assertEquals("real", t.sort().name().toString(), "real literal should have sort real");
        assertEquals(RealLDT.REAL_NUMBERS_NAME, t.op().name(),
            "real literal should be wrapped in the __R symbol");
    }

    /**
     * Parser and pretty-printer are inverse: a literal prints back to its canonical decimal form
     * (with the {@code r} suffix), and re-parsing that form yields the very same term.
     */
    @Test
    void realLiteralRoundTripsThroughParserAndPrinter() {
        // input -> canonical printed form (trailing zeros stripped)
        String[][] cases = {
            { "1.25r", "1.25r" },
            { "-0.5r", "-0.5r" },
            { "0.001r", "0.001r" },
            { "100r", "100r" },
            { "-12.0r", "-12r" },
            { "0.0r", "0r" },
            { "3.14159r", "3.14159r" },
        };
        KeyIO io = io();
        for (String[] c : cases) {
            JTerm t = io.parseExpression(c[0]);
            assertEquals(c[1], LogicPrinter.quickPrintTerm(t, io.getServices()).trim(),
                "printed form of " + c[0]);
            assertEquals(t, io.parseExpression(c[1]),
                "re-parsing the printed form of " + c[0] + " must yield the same term");
        }
    }
}

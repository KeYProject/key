/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.nparser;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.rule.TacletForTests;
import de.uka.ilkd.key.util.ExceptionTools;

import org.key_project.util.parsing.Location;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Issue #3867: a missing/mistyped {@code \endmodality} should be reported at the unterminated
 * modality's opening, not run on to the next, unrelated {@code \endmodality} (which produced a
 * confusing error far from the actual mistake).
 */
class Issue3867Test {

    private static void load(String src) throws Exception {
        Services s = TacletForTests.services().copy(false);
        new KeyIO(s, s.getNamespaces()).load(src).loadComplete();
    }

    @Test
    void missingEndmodalityIsReportedAtTheModalityOpening() {
        // The \find modality's \endmodality (line 4) is mistyped as "endm". Without the fix the
        // lexer ran on to the \replacewith's \endmodality (line 5) and reported there.
        String src = """
                \\rules { test {
                   \\schemaVar \\modalOperator {diamond, box} #allmodal;
                   \\find(
                       \\modality{#allmodal}{}endm (true))
                   \\replacewith(\\modality{#allmodal}{}\\endmodality(true))
                }; }""";
        Throwable ex = assertThrows(Throwable.class, () -> load(src));

        Location loc = assertDoesNotThrow(() -> ExceptionTools.getLocation(ex));
        assertNotNull(loc, "a location should be reported");
        assertEquals(4, loc.getPosition().line(),
            "the error should point at the unterminated modality (line 4), not the later "
                + "'\\endmodality' on line 5");

        String msg = ExceptionTools.getMessage(ex);
        assertTrue(msg.contains("endmodality") || msg.toLowerCase().contains("not terminated"),
            "message should mention the missing \\endmodality, got: " + msg);
    }

    @Test
    void modalityKeywordsInCommentsAreIgnored() {
        // A modality-opening keyword inside a Java line comment must not be mistaken for a nested
        // modality (it is part of the program text, not KeY syntax).
        assertDoesNotThrow(() -> load("""
                \\rules { r {
                   \\find(\\<{ int x = 0; // use \\modality here
                   }\\>(true)) \\replacewith(\\<{}\\>(true))
                }; }"""));
        // ... and inside a block comment. This also covers the (previously broken) case of a
        // *closing* keyword inside a comment, which used to terminate the modality early.
        assertDoesNotThrow(() -> load("""
                \\rules { r {
                   \\find(\\<{ /* not a real close \\> here */ int y = 0; }\\>(true))
                   \\replacewith(\\<{}\\>(true))
                }; }"""));
    }

    @Test
    void wellFormedModalitiesStillParse() {
        // generic, diamond and box forms must be unaffected by the new check
        assertDoesNotThrow(() -> load("""
                \\rules { test {
                   \\schemaVar \\modalOperator {diamond, box} #allmodal;
                   \\find(\\modality{#allmodal}{}\\endmodality(true))
                   \\replacewith(\\modality{#allmodal}{}\\endmodality(true))
                }; }"""));
        assertDoesNotThrow(() -> load("""
                \\rules { test {
                   \\find(\\<{}\\>(true)) \\replacewith(\\<{}\\>(true))
                }; }"""));
        assertDoesNotThrow(() -> load("""
                \\rules { test {
                   \\find(\\[{}\\](true)) \\replacewith(\\[{}\\](true))
                }; }"""));
    }
}

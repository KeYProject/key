/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.nparser;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.rule.TacletForTests;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Regression guards for issue #1536 (parsing of nested updates).
 *
 * <p>
 * The originally reported cryptic error ("Not a legal lhs: ...") for an update whose left-hand
 * side is itself an update application is now a clear, actionable message, and the bracketed form
 * the message suggests parses correctly.
 */
class NestedUpdateParsingTest {

    private static void load(String problem) throws Exception {
        Services services = TacletForTests.services().copy(false);
        KeyIO io = new KeyIO(services, services.getNamespaces());
        io.load("\\programVariables { int a,b; }\n\\problem { " + problem + " }")
                .loadCompleteProblem();
    }

    @Test
    void unbracketedNestedUpdateGivesHelpfulError() {
        Exception ex = assertThrows(Exception.class,
            () -> load("{{a:=3} b:=a}( a = 1 & b = 3 )"));
        assertTrue(String.valueOf(ex.getMessage()).contains("bracketed version"),
            "expected a hint to use the bracketed form, got: " + ex.getMessage());
    }

    @Test
    void bracketedNestedUpdateParses() {
        assertDoesNotThrow(() -> load("{{a:=3} (b:=a)}( a = 1 & b = 3 )"));
    }
}

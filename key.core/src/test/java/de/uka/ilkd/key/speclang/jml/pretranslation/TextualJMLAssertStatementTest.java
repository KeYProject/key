/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang.jml.pretranslation;

import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.speclang.njml.PreParser;

import org.key_project.util.collection.ImmutableList;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;


public class TextualJMLAssertStatementTest {
    private static ImmutableList<TextualJMLConstruct> parseMethodLevel(String ms) {
        return new PreParser().parseMethodLevel(ms, null, Position.newOneBased(1, 1));
    }

    private static void assertTextRepr(String input, String text) {
        var constructs = parseMethodLevel(input);
        assertNotNull(constructs);
        assertEquals(1, constructs.size());
        assertTrue(constructs.head() instanceof TextualJMLAssertStatement);
        var jmlAssert = (TextualJMLAssertStatement) constructs.head();
        var builder = new StringBuilder();
        TextualJMLAssertStatement.ruleContextToText(builder, jmlAssert.getContext().first);
        assertEquals(builder.toString(), text);
    }

    @Test
    public void testTextRepr() {
        assertTextRepr("//@ assert true;", "assert true ;");
        assertTextRepr("//@ assert 1 + 2 == 3 && 2 != 3;", "assert 1 + 2 == 3 && 2 != 3 ;");
        assertTextRepr("//@ assert (\\forall int j; 0 <= j < 10; true);",
            "assert ( \\forall int j ; 0 <= j < 10 ; true ) ;");
        assertTextRepr(
            "//@ assert (\\forall int j; 0 <= j < 10; (\\exists int k; 0 <= k < 10; j == k));",
            "assert ( \\forall int j ; 0 <= j < 10 ; ( \\exists int k ; 0 <= k < 10 ; j == k ) ) ;");
    }
}

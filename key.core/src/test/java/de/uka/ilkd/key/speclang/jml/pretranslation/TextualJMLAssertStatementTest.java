/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang.jml.pretranslation;

import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.speclang.njml.PreParser;

import org.key_project.util.collection.ImmutableList;

import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.CsvSource;

import static org.junit.jupiter.api.Assertions.*;


public class TextualJMLAssertStatementTest {
    private static ImmutableList<TextualJMLConstruct> parseMethodLevel(String ms) {
        return new PreParser(true).parseMethodLevel(ms, null, Position.newOneBased(1, 1));
    }

    @ParameterizedTest
    @CsvSource(delimiter = '#',
        textBlock = """
                //@ assert true; # true;
                //@ assert 1 + 2 == 3 && 2 != 3; # 1 + 2 == 3 && 2 != 3;
                //@ assert (\\forall int j; 0 <= j < 10; true); # (\\forall int j; 0 <= j < 10; true);
                //@ assert (\\forall int j; 0 <= j < 10; (\\exists int k; 0 <= k < 10; j == k)); # (\\forall int j; 0 <= j < 10; (\\exists int k; 0 <= k < 10; j == k));
                """)
    void assertTextRepr(String input, String text) {
        var constructs = parseMethodLevel(input);
        assertNotNull(constructs);
        assertEquals(1, constructs.size());
        assertInstanceOf(TextualJMLAssertStatement.class, constructs.head());
        var jmlAssert = (TextualJMLAssertStatement) constructs.head();
        assertEquals(text, jmlAssert.getContext().getText());
    }
}

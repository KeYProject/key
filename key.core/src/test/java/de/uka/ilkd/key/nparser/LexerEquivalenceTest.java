/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.nparser;

import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.Token;
import org.junit.jupiter.api.Test;

import static org.assertj.core.api.Assertions.assertThat;

/**
 * Pins exact lexer equivalence properties of the KeY grammar: backslash escapes inside
 * modality-body strings survive lexing, and the lexer does not retype numerals.
 */
class LexerEquivalenceTest {

    private Token tokenAt(String input, int index) {
        JavaKeYLexer lexer = new JavaKeYLexer(CharStreams.fromString(input));
        Token token = null;
        for (int i = 0; i <= index; i++) {
            token = lexer.nextToken();
        }
        return token;
    }

    @Test
    void modalityStringKeepsBackslashEscapesIntact() {
        String text = tokenAt("\\<{ x = \"a\\nb\"; }\\>", 0).getText();
        assertThat(text).contains("a\\nb");
    }

    @Test
    void modalityStringKeepsDoubleBackslashesIntact() {
        String text = tokenAt("\\<{ s = \"C:\\\\temp\\\\x\"; }\\>", 0).getText();
        assertThat(text).contains("C:\\\\temp\\\\x");
    }

    @Test
    void intFollowedByParenKeepsItsType() {
        Token first = tokenAt("(123(", 1);
        assertThat(first.getType()).isEqualTo(JavaKeYLexer.INT_LITERAL);
    }

    @Test
    void intFollowedByNbspThenParenStaysInt() {
        Token first = tokenAt("123\u00A0(", 0);
        assertThat(first.getType()).isEqualTo(JavaKeYLexer.INT_LITERAL);
        Token second = tokenAt("123\u00A0(", 1);
        assertThat(second.getType()).isEqualTo(JavaKeYLexer.LPAREN);
    }
}

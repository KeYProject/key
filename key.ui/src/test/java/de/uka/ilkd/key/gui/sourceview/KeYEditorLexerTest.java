/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.sourceview;

import java.util.List;

import org.junit.jupiter.api.Test;

import static org.assertj.core.api.Assertions.assertThat;

/**
 * Tests that the tokens produced by {@link KeYEditorLexer} tile the highlighted text.
 * <p>
 * {@link SourceHighlightDocument} applies the tokens by successively advancing an offset by the
 * token length. Tokens therefore have to cover every character of the text, including the
 * whitespace that the underlying ANTLR lexer skips.
 */
class KeYEditorLexerTest {

    @Test
    void tokensCoverTheWholeText() {
        String text = "\\problem {\n    \\forall int x; x >= 0;\n}\n   ";

        List<SourceHighlightDocument.Token> tokens = new KeYEditorLexer().applyTo(text);

        assertThat(tokens.stream().mapToInt(SourceHighlightDocument.Token::len).sum())
                .isEqualTo(text.length());
    }

    @Test
    void keywordIsHighlightedAtItsSourcePosition() {
        String text = "\\problem {\n  \\forall int x; true\n}";
        List<SourceHighlightDocument.Token> tokens = new KeYEditorLexer().applyTo(text);

        int forallPosition = text.indexOf("\\forall");
        SourceHighlightDocument.Token tokenAtForall = tokenStartingAt(tokens, forallPosition);

        assertThat(tokenAtForall.len()).isEqualTo("\\forall".length());
        // both "\\problem" and "\\forall" are primary keywords and share one attribute set
        assertThat(tokenAtForall.attributes()).isEqualTo(tokens.get(0).attributes());
    }

    @Test
    void keywordAfterNonBmpCharacterIsHighlightedAtItsSourcePosition() {
        // U+1F600 lies outside the BMP: one code point, but two chars in the document
        String text = "\\sorts { S; }\n// 😀\n\\problem { true }";
        List<SourceHighlightDocument.Token> tokens = new KeYEditorLexer().applyTo(text);

        int problemPosition = text.indexOf("\\problem");
        SourceHighlightDocument.Token tokenAtProblem = tokenStartingAt(tokens, problemPosition);

        assertThat(tokenAtProblem.len()).isEqualTo("\\problem".length());
        // both "\\sorts" and "\\problem" are primary keywords and share one attribute set
        assertThat(tokenAtProblem.attributes()).isEqualTo(tokens.get(0).attributes());
        assertThat(tokens.stream().mapToInt(SourceHighlightDocument.Token::len).sum())
                .isEqualTo(text.length());
    }

    /**
     * Returns the token that starts at the given character position, assuming the tokens tile the
     * text starting at offset zero.
     */
    private static SourceHighlightDocument.Token tokenStartingAt(
            List<SourceHighlightDocument.Token> tokens, int position) {
        int offset = 0;
        for (SourceHighlightDocument.Token token : tokens) {
            if (offset == position) {
                return token;
            }
            offset += token.len();
        }
        throw new AssertionError("No token starts at position " + position);
    }
}

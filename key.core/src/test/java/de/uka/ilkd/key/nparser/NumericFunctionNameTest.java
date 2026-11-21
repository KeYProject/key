/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.nparser;

import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.tree.Trees;
import org.junit.jupiter.api.Test;

import static org.assertj.core.api.Assertions.assertThat;
import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;

/**
 * Numerals are valid names in KeY: the integer literal constructors are declared as
 * {@code 0(numbers) ... 9(numbers)} and applied in terms such as {@code Z(0(#))}. The lexer keeps
 * numerals as {@code INT_LITERAL}; the parser accepts them as identifiers where needed.
 */
class NumericFunctionNameTest {

    @Test
    void numericFunctionApplicationParses() {
        assertDoesNotThrow(() -> ParsingFacade.parseExpression(CharStreams.fromString("Z(0(#))")));
        assertDoesNotThrow(
            () -> ParsingFacade.parseExpression(CharStreams.fromString("C(2(2(1(#))))")));
        assertDoesNotThrow(() -> ParsingFacade.parseExpression(CharStreams.fromString("1(#)")));
    }

    @Test
    void numericFunctionApplicationIsAnAccessTerm() {
        KeyAst.Term term =
            ParsingFacade.parseExpression(CharStreams.fromString("Z(0(#))"));
        assertThat(Trees.findAllRuleNodes(term.ctx, JavaKeYParser.RULE_accessterm)).isNotEmpty();
    }

    @Test
    void bareNumeralIsStillALiteral() {
        KeyAst.Term term = ParsingFacade.parseExpression(CharStreams.fromString("42"));
        assertThat(Trees.findAllRuleNodes(term.ctx, JavaKeYParser.RULE_accessterm)).isEmpty();
        assertThat(Trees.findAllRuleNodes(term.ctx, JavaKeYParser.RULE_integer)).isNotEmpty();
    }

    @Test
    void numericDeclarationsParse() {
        String file = """
                \\functions {
                    numbers 0(numbers);
                    numbers 1(numbers);
                }
                """;
        assertDoesNotThrow(() -> ParsingFacade.parseFile(CharStreams.fromString(file)));
    }

    @Test
    void numericNamesAreAcceptedInIdentifierPositions() {
        String file = """
                \\sorts { 1; }
                \\functions { int 1(1); }
                \\programVariables { int 2; }
                """;
        assertDoesNotThrow(() -> ParsingFacade.parseFile(CharStreams.fromString(file)));
    }

    @Test
    void nbspBeforeArgumentListIsWhitespace() {
        // the lexer skips NBSP as whitespace, so the numeral followed by a call is a numeric name
        assertDoesNotThrow(
            () -> ParsingFacade.parseExpression(CharStreams.fromString("0\u00A0(#)")));
    }

    @Test
    void matchIdentifiersAreStillValidAccessTermNames() {
        // proof-script terms such as ?find(...), ?focus(...) and a bare ? are MATCH_IDENT names
        assertDoesNotThrow(
            () -> ParsingFacade.parseExpression(CharStreams.fromString("?find(1+1)")));
        assertDoesNotThrow(
            () -> ParsingFacade.parseExpression(CharStreams.fromString("?focus(a+0)")));
        assertDoesNotThrow(() -> ParsingFacade.parseExpression(CharStreams.fromString("? = b")));
    }
}

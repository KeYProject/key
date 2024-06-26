/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.tacletbuilder.branchlabel;

import java.util.ArrayList;
import java.util.List;

import de.uka.ilkd.key.nparser.KeYLexer;
import de.uka.ilkd.key.nparser.ParsingFacade;

import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonToken;
import org.antlr.v4.runtime.IntStream;
import org.antlr.v4.runtime.Token;

/**
 * Parser for branch labels.
 * <p>
 * Branch labels are strings that include dynamic function calls marked by escaped tokens.
 * It exploits the key parser to tokenize the given string and to construct a list of branch naming
 * functions.
 * </p>
 *
 * @author Alexander Weigl
 * @version 1 (20.03.23)
 */
class MiniLabelParser {

    final KeYLexer stream;
    int current = -1;
    final List<? extends Token> tokens;
    Token token;

    public MiniLabelParser(String text) {
        stream = ParsingFacade.createLexer(CharStreams.fromString(text));
        tokens = stream.getAllTokens();
        consume();
    }

    public BranchNamingFunction parse() {
        final List<BranchNamingFunction> branchNamingFunctions = new ArrayList<>();
        do {
            if (token.getType() == KeYLexer.ESC_IDENT) {
                branchNamingFunctions.add(parseBranchLabel());
            } else {
                branchNamingFunctions.add(new SimpleStringLabel(token.getText()));
                consume();
            }
        } while (token.getType() != IntStream.EOF);
        return new CompositionalBranchNamingFunction(branchNamingFunctions);
    }

    private BranchNamingFunction parseBranchLabel() {
        var args = new ArrayList<String>();
        args.add(token.getText());
        consumeWS();
        if (token.getType() == KeYLexer.LPAREN) {
            consumeWS();
            if (token.getType() != KeYLexer.RPAREN) {
                if (token.getType() != KeYLexer.IDENT)
                    throw new IllegalStateException("expected text after '(' but got: " + token);
                args.add(token.getText());
                consumeWS();
                do {
                    if (token.getType() == KeYLexer.COMMA) {
                        consumeWS();
                        if (token.getType() != KeYLexer.IDENT)
                            throw new IllegalArgumentException("Expected text after comma");
                        args.add(token.getText());
                        consumeWS();
                    } else if (token.getType() == KeYLexer.RPAREN) {
                        break;
                    } else {
                        throw new IllegalArgumentException("Unexpected token: " + token);
                    }
                } while (token.getType() != KeYLexer.RPAREN);
            }
            consume();
        }
        var factory = BranchNamingFunctions.get(args.get(0));
        if (factory == null) {
            throw new IllegalStateException(
                "A BranchNamingFunction with name " + args.get(0) + " is unknown.");
        }
        return factory.apply(args);
    }

    private void consumeWS() {
        do {
            consume();
        } while (token.getType() == KeYLexer.WS);
    }

    private void consume() {
        current++;
        if (current >= tokens.size()) {
            token = new CommonToken(Token.EOF);
        } else {
            token = tokens.get(current);
        }
    }
}

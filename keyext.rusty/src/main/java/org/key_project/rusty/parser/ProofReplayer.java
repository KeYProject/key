/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.parser;

import java.net.URI;
import java.util.ArrayDeque;
import java.util.Deque;
import java.util.LinkedHashMap;
import java.util.Map;

import org.key_project.rusty.proof.io.IProofFileParser;

import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.Token;
import org.jspecify.annotations.NonNull;

public class ProofReplayer {
    /**
     * This map is for the translation between symbols in the sexpr and the corresponding proof tag.
     */
    private static final Map<String, IProofFileParser.ProofElementID> proofSymbolElementId =
        new LinkedHashMap<>(32);

    static {
        for (IProofFileParser.ProofElementID id : IProofFileParser.ProofElementID.values()) {
            proofSymbolElementId.put(id.getRawName(), id);
        }
    }

    private ProofReplayer() {
    }

    /**
     * Replays the proof represented by the expression given in the {@link CharStream} after the
     * position of the {@code token}.
     *
     * @param token the "\proof" with in the input stream
     * @param input a valid input stream
     * @param prl the proof replayer instance
     * @param source the source of the stream, used for producing exceptions with locations
     * @see #run(CharStream, IProofFileParser, int, URI)
     */
    public static void run(@NonNull Token token, CharStream input, IProofFileParser prl,
            URI source) {
        input.seek(1 + token.getStopIndex()); // ends now on \proof|
        run(input, prl, token.getLine(), source);
    }

    /**
     * Replays the proof behind the given {@code input}. This method uses the {@link KeYLexer} to
     * lex input stream, and parse them manually by consuming the tokens. It singals to the given
     * {@link IProofFileParser} at start or end of an expr.
     * <p>
     * Avoid the usage of a parser, avoids also the construction of an ASTs.
     *
     * @param input a valid input stream
     * @param prl the proof replayer interface
     * @param startLine the starting of the sexpr needed for {@code prl}
     * @param source the source of the stream, used for producing exceptions with locations
     */
    public static void run(CharStream input, IProofFileParser prl, final int startLine,
            URI source) {
        KeYRustyLexer lexer = ParsingFacade.createLexer(input);
        CommonTokenStream stream = new CommonTokenStream(lexer);
        ArrayDeque<IProofFileParser.ProofElementID> stack = new ArrayDeque<>(); // currently open
        // proof
        // elements
        Deque<Integer> posStack = new ArrayDeque<>(); // stack of opened commands position
        while (true) {
            int type = stream.LA(1); // current token type
            switch (type) {
            case KeYRustyLexer.LPAREN -> {
                // expected "(" <id> ["string"]
                stream.consume(); // consume the "("
                Token idToken = stream.LT(1); // element id
                IProofFileParser.ProofElementID cur = proofSymbolElementId.get(idToken.getText());
                if (cur == null) {
                    /*
                     * Location loc =
                     * new Location(source, Position.fromToken(idToken).offsetLine(startLine - 1));
                     * throw new LocatableException("Unknown proof element: " + idToken.getText(),
                     * loc);
                     */
                    throw new RuntimeException("Unknown proof element");
                }
                stream.consume();
                String arg = null;
                int pos = idToken.getLine() + startLine;
                if (stream.LA(1) == KeYRustyLexer.STRING_LITERAL) {
                    // argument was given
                    arg = stream.LT(1).getText();
                    arg = unescape(arg.substring(1, arg.length() - 1));
                    stream.consume();// throw string away
                }
                prl.beginExpr(cur, arg);
                stack.push(cur);
                posStack.push(pos);
            }
            case KeYRustyLexer.RPAREN -> {
                prl.endExpr(stack.pop(), posStack.pop());
                stream.consume();
            }
            case KeYRustyLexer.EOF -> {
                return;
            }
            default -> stream.consume();
            }
        }
    }

    private static String unescape(String text) {
        return text.replace("\\\\", "\\").replace("\\\"", "\"");
    }
}

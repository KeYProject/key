/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.nparser;

import java.net.URI;
import java.net.URL;
import java.util.*;
import javax.annotation.Nonnull;

import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.proof.io.IProofFileParser;
import de.uka.ilkd.key.util.parsing.LocatableException;

import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.Token;

/**
 * A short little hack, but completely working and fast, for replaying proofs inside KeY files.
 * <p>
 * This class avoids using the {@link KeYParser} and building a parse tree. It uses only the
 * {@link KeYLexer} to analyze the sexpr which described the applied taclet application.
 *
 * @author Alexander Weigl
 * @version 1 (12/5/19)
 * @see #run(Token, CharStream, IProofFileParser, URL)
 */
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
    public static void run(@Nonnull Token token, CharStream input, IProofFileParser prl,
            URI source) {
        input.seek(1 + token.getStopIndex()); // ends now on \proof|
        run(input, prl, token.getLine(), source);
    }

    /**
     * Replays the proof behind the given {@code input}. This method uses the {@link KeYLexer} to
     * lex input stream, and parse them manually by consuming the tokens. It singals to the given
     * {@link IProofFileParser} at start or end of an expr.
     *
     * Avoid the usage of a parser, avoids also the construction of an ASTs.
     *
     * @param input a valid input stream
     * @param prl the proof replayer interface
     * @param startLine the starting of the sexpr needed for {@code prl}
     * @param source the source of the stream, used for producing exceptions with locations
     */
    public static void run(CharStream input, IProofFileParser prl, final int startLine,
            URI source) {
        KeYLexer lexer = ParsingFacade.createLexer(input);
        CommonTokenStream stream = new CommonTokenStream(lexer);
        ArrayDeque<IProofFileParser.ProofElementID> stack = new ArrayDeque<>(); // currently open
                                                                                // proof
        // elements
        Deque<Integer> posStack = new ArrayDeque<>(); // stack of opened commands position
        while (true) {
            int type = stream.LA(1); // current token type
            switch (type) {
            case KeYLexer.LPAREN:
                // expected "(" <id> ["string"]
                stream.consume(); // consume the "("
                Token idToken = stream.LT(1); // element id
                IProofFileParser.ProofElementID cur = proofSymbolElementId.get(idToken.getText());

                if (cur == null) {
                    Location loc =
                        new Location(source, Position.fromToken(idToken).offsetLine(startLine - 1));
                    throw new LocatableException("Unknown proof element: " + idToken.getText(),
                        loc);
                }
                stream.consume();

                String arg = null;
                int pos = idToken.getLine() + startLine;
                if (stream.LA(1) == KeYLexer.STRING_LITERAL) {
                    // argument was given
                    arg = stream.LT(1).getText();
                    arg = unescape(arg.substring(1, arg.length() - 1));
                    stream.consume();// throw string away
                }

                prl.beginExpr(cur, arg);
                stack.push(cur);
                posStack.push(pos);
                break;
            case KeYLexer.RPAREN:
                prl.endExpr(stack.pop(), posStack.pop());
                stream.consume();
                break;
            case KeYLexer.EOF:
                return;
            default:
                stream.consume();
            }
        }
    }

    private static String unescape(String text) {
        return text.replace("\\\\", "\\").replace("\\\"", "\"");
    }
}

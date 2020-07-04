package de.uka.ilkd.key.nparser;

import de.uka.ilkd.key.proof.io.IProofFileParser;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.Token;
import org.jetbrains.annotations.NotNull;

import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Stack;

/**
 * A short little hack, but completely working and fast, for replaying proofs inside KeY files.
 * <p>
 * This class avoids using the {@link KeYParser} and building a parse tree. It uses only the {@link KeYLexer}
 * to analyze the sexpr which described the applied taclet application.
 *
 * @author Alexander Weigl
 * @version 1 (12/5/19)
 * @see #run(Token, CharStream, IProofFileParser)
 */
public class ProofReplayer {
    /**
     * This map is for the translation between symbols in the sexpr and the corresponding proof tag.
     */
    private static final Map<String, IProofFileParser.ProofElementID> proofSymbolElementId = new LinkedHashMap<>(32);

    static {
        for (IProofFileParser.ProofElementID id : IProofFileParser.ProofElementID.values()) {
            proofSymbolElementId.put(id.getRawName(), id);
        }
    }


    /**
     * Replays the proof represented by the expression given in the {@link CharStream} after the position of the
     * {@code token}.
     *
     * @param token the "\proof" with in the input stream
     * @param input a valid input stream
     * @param prl   the proof replayer instance
     * @see #run(CharStream, IProofFileParser, int)
     */
    public static void run(@NotNull Token token, CharStream input, IProofFileParser prl) {
        input.seek(1 + token.getStopIndex()); // ends now on \proof|
        run(input, prl, token.getLine());
    }

    /**
     * Replays the proof behind the given {@code input}.
     * This method uses the {@link KeYLexer} to lex input stream, and parse them manually
     * by consuming the tokens. It singals to the given {@link IProofFileParser} at start or end of an expr.
     *
     * Avoid the usage of a parser, avoids also the construction of an ASTs.
     *
     * @param input     a valid input stream
     * @param prl       the proof replayer interface
     * @param startLine the starting of the sexpr needed for {@code prl}
     */
    public static void run(CharStream input, IProofFileParser prl, final int startLine) {
        KeYLexer lexer = ParsingFacade.lex(input);
        CommonTokenStream stream = new CommonTokenStream(lexer);
        Stack<IProofFileParser.ProofElementID> stack = new Stack<>(); //currently open proof elements
        Stack<Integer> posStack = new Stack<>(); // stack of opened commands position
        while (true) {
            int type = stream.LA(1); //current token type
            switch (type) {
                case KeYLexer.LPAREN:
                    //expected "(" <id> ["string"]
                    stream.consume(); //consume the "("
                    Token idToken = stream.LT(1); // element id
                    IProofFileParser.ProofElementID cur = proofSymbolElementId.get(idToken.getText());
                    stream.consume();

                    String arg = null;
                    int pos = idToken.getLine() + startLine;
                    if (stream.LA(1) == KeYLexer.STRING_LITERAL) {
                        //argument was given
                        arg = stream.LT(1).getText();
                        arg = unescape(arg.substring(1, arg.length() - 1));
                        stream.consume();//throw string away
                    }

                    prl.beginExpr(cur, arg);
                    //System.out.format("Emit: %s %s%n", cur, arg);
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
        return text
                .replace("\\\\", "\\")
                .replace("\\\"", "\"");
    }
}

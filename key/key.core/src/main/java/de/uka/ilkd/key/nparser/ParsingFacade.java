package de.uka.ilkd.key.nparser;

import de.uka.ilkd.key.nparser.builder.ChoiceFinder;
import de.uka.ilkd.key.proof.io.RuleSource;
import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.atn.ATNConfigSet;
import org.antlr.v4.runtime.dfa.DFA;
import javax.annotation.Nonnull;

import java.io.BufferedInputStream;
import java.io.File;
import java.io.IOException;
import java.net.URL;
import java.nio.channels.Channels;
import java.nio.channels.ReadableByteChannel;
import java.nio.charset.Charset;
import java.nio.charset.CodingErrorAction;
import java.nio.file.Path;
import java.util.*;

/**
 * This facade provides low-level access to the ANTLR4 Parser and Lexer.
 * <p>
 * You should only use it if you need access to the parse trees instead of terms or taclet structure.
 *
 * @author Alexander Weigl
 * @version 1 (19.08.19)
 */
public abstract class ParsingFacade {
    /**
     * Use this function to retrieve the {@link ParserRuleContext} inside and {@link KeyAst} object.
     * <b>The use of this method is discourage and should be avoided in all high level scenarios.</b>
     *
     * @param ast a key ast object
     * @param <T> parse tree type
     * @return the {@link ParserRuleContext} inside the given ast object.
     */
    public static <T extends ParserRuleContext> @Nonnull T getParseRuleContext(@Nonnull KeyAst<T> ast) {
        return ast.ctx;
    }

    public static List<KeyAst.File> parseFiles(URL url) throws IOException {
        List<KeyAst.File> ctxs = new LinkedList<>();
        Stack<URL> queue = new Stack<>();
        queue.add(url);
        Set<URL> reached = new HashSet<>();

        while (!queue.isEmpty()) {
            url = queue.pop();
            reached.add(url);
            KeyAst.File ctx = parseFile(url);
            ctxs.add(ctx);
            Collection<RuleSource> includes = ctx.getIncludes(url).getRuleSets();
            for (RuleSource u : includes) {
                if (!reached.contains(u.url())) {
                    queue.add(u.url());
                }
            }
        }
        return ctxs;
    }

    /**
     * Extracts the choice information from the given the parsed files {@code ctxs}.
     *
     * @param ctxs non-null list
     * @return
     */
    public static @Nonnull ChoiceInformation getChoices(@Nonnull List<KeyAst.File> ctxs) {
        ChoiceInformation ci = new ChoiceInformation();
        ChoiceFinder finder = new ChoiceFinder(ci);
        ctxs.forEach(it -> it.accept(finder));
        return ci;
    }

    private static KeYParser createParser(CharStream stream) {
        KeYParser p = new KeYParser(new CommonTokenStream(createLexer(stream)));
        p.removeErrorListeners();
        p.addErrorListener(p.getErrorReporter());
        return p;
    }

    public static KeYLexer createLexer(Path file) throws IOException {
        return createLexer(CharStreams.fromPath(file));
    }

    public static KeYLexer createLexer(CharStream stream) {
        return new KeYLexer(stream);
    }

    public static KeyAst.File parseFile(URL url) throws IOException {
        //long start = System.currentTimeMillis();
        try (BufferedInputStream is = new BufferedInputStream(url.openStream());
             ReadableByteChannel channel = Channels.newChannel(is)) {
            CodePointCharStream stream = CharStreams.fromChannel(
                    channel,
                    Charset.defaultCharset(),
                    4096,
                    CodingErrorAction.REPLACE,
                    url.toString(),
                    -1);
            return parseFile(stream);
        } finally {
            //long stop = System.currentTimeMillis();
            //System.err.printf("PARSING %s took %d ms\n", url, stop - start);
        }
    }

    public static KeyAst.File parseFile(Path file) throws IOException {
        return parseFile(CharStreams.fromPath(file));
    }

    public static KeyAst.File parseFile(File file) throws IOException {
        return parseFile(file.toPath());
    }

    public static KeyAst.File parseFile(CharStream stream) {
        KeYParser p = createParser(stream);
        KeYParser.FileContext ctx = p.file();
        p.getErrorReporter().throwException();
        return new KeyAst.File(ctx);
    }

    public static KeyAst.Term parseExpression(CharStream stream) {
        KeYParser p = createParser(stream);
        KeYParser.TermContext term = p.termEOF().term();
        p.getErrorReporter().throwException();
        return new KeyAst.Term(term);
    }

    public static KeyAst.Seq parseSequent(CharStream stream) {
        KeYParser p = createParser(stream);
        KeyAst.Seq seq = new KeyAst.Seq(p.seqEOF().seq());
        p.getErrorReporter().throwException();
        return seq;
    }

    /**
     * Translate a given context of a {@code string_value} grammar rule into a the literal value.
     * In particular it truncates, and substitutes quote escapes {@code \"}.
     *
     * @param ctx non-null context
     * @return non-null string
     */
    public static @Nonnull String getValue(@Nonnull KeYParser.String_valueContext ctx) {
        return ctx.getText().substring(1, ctx.getText().length() - 1)
                .replace("\\\"", "\"")
                .replace("\\\\", "\\");
    }

    /**
     * Parse the id declaration. This a seldom special case somewhere in key.ui.
     * <p>
     * <b>Use is discourage.</b>
     *
     * @param stream
     * @return
     * @deprecated
     */
    public static KeYParser.Id_declarationContext parseIdDeclaration(CharStream stream) {
        KeYParser p = createParser(stream);
        return p.id_declaration();
    }
}

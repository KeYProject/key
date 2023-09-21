/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.nparser;

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
import javax.annotation.Nonnull;
import javax.annotation.Nullable;

import de.uka.ilkd.key.nparser.builder.ChoiceFinder;
import de.uka.ilkd.key.proof.io.RuleSource;

import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.atn.PredictionMode;
import org.antlr.v4.runtime.misc.ParseCancellationException;
import org.antlr.v4.runtime.tree.TerminalNode;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * This facade provides low-level access to the ANTLR4 Parser and Lexer.
 * <p>
 * You should only use it if you need access to the parse trees instead of terms or taclet
 * structure.
 *
 * @author Alexander Weigl
 * @version 1 (19.08.19)
 */
public final class ParsingFacade {
    private static final Logger LOGGER = LoggerFactory.getLogger(ParsingFacade.class);

    private ParsingFacade() {
    }

    /**
     * Use this function to retrieve the {@link ParserRuleContext} inside and {@link KeyAst} object.
     * <b>The use of this method is discourage and should be avoided in all high level
     * scenarios.</b>
     *
     * @param ast a key ast object
     * @param <T> parse tree type
     * @return the {@link ParserRuleContext} inside the given ast object.
     */
    @Nonnull
    public static <T extends ParserRuleContext> T getParseRuleContext(@Nonnull KeyAst<T> ast) {
        return ast.ctx;
    }

    public static List<KeyAst.File> parseFiles(URL url) throws IOException {
        List<KeyAst.File> ctxs = new LinkedList<>();
        ArrayDeque<URL> queue = new ArrayDeque<>();
        queue.push(url);
        Set<URL> reached = new HashSet<>();

        while (!queue.isEmpty()) {
            url = queue.pop();
            reached.add(url);
            KeyAst.File ctx = parseFile(url);
            ctxs.add(ctx);
            Collection<RuleSource> includes = ctx.getIncludes(url).getRuleSets();
            for (RuleSource u : includes) {
                if (!reached.contains(u.url())) {
                    queue.push(u.url());
                }
            }
        }
        return ctxs;
    }

    /**
     * Extracts the choice information from the given the parsed files {@code ctxs}.
     *
     * @param ctxs non-null list
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
        long start = System.currentTimeMillis();
        try (BufferedInputStream is = new BufferedInputStream(url.openStream());
                ReadableByteChannel channel = Channels.newChannel(is)) {
            CodePointCharStream stream = CharStreams.fromChannel(channel, Charset.defaultCharset(),
                4096, CodingErrorAction.REPLACE, url.toString(), -1);
            return parseFile(stream);
        } finally {
            long stop = System.currentTimeMillis();
            LOGGER.debug("PARSING {} took {} ms", url, stop - start);
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

        p.getInterpreter().setPredictionMode(PredictionMode.SLL);
        // we don't want error messages or recovery during first try
        p.removeErrorListeners();
        p.setErrorHandler(new BailErrorStrategy());
        KeYParser.FileContext ctx;
        try {
            ctx = p.file();
        } catch (ParseCancellationException ex) {
            LOGGER.warn("SLL was not enough");
            p = createParser(stream);
            ctx = p.file();
        }

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
     * Translate a given context of a {@code string_value} grammar rule into a the literal value. In
     * particular it truncates, and substitutes quote escapes {@code \"}.
     *
     * @param ctx non-null context
     * @return non-null string
     */
    public static @Nonnull String getValueDocumentation(
            @Nonnull KeYParser.String_valueContext ctx) {
        return ctx.getText().substring(1, ctx.getText().length() - 1).replace("\\\"", "\"")
                .replace("\\\\", "\\");
    }

    /**
     * Parse the id declaration. This a seldom special case somewhere in key.ui.
     * <p>
     * <b>Use is discourage.</b>
     *
     * @deprecated
     */
    @Deprecated
    public static KeYParser.Id_declarationContext parseIdDeclaration(CharStream stream) {
        KeYParser p = createParser(stream);
        return p.id_declaration();
    }

    @Nullable
    public static String getValueDocumentation(@Nullable TerminalNode docComment) {
        if (docComment == null) {
            return null;
        }
        String value = docComment.getText();
        return value.substring(3, value.length() - 2);// remove leading "/*!" and trailing "*/"
    }
}

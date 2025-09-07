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

import de.uka.ilkd.key.nparser.builder.ChoiceFinder;
import de.uka.ilkd.key.proof.io.RuleSource;
import de.uka.ilkd.key.settings.Configuration;
import de.uka.ilkd.key.speclang.PositionedString;
import de.uka.ilkd.key.util.parsing.BuildingException;

import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.atn.PredictionMode;
import org.antlr.v4.runtime.misc.ParseCancellationException;
import org.antlr.v4.runtime.tree.TerminalNode;
import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.NullMarked;
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
@NullMarked
public final class ParsingFacade {
    private static final Logger LOGGER = LoggerFactory.getLogger(ParsingFacade.class);

    private ParsingFacade() {
    }

    /**
     * Use this function to retrieve the {@link ParserRuleContext} inside an {@link KeyAst} object.
     * <b>The use of this method is discouraged and should be avoided in all high level
     * scenarios.</b>
     *
     * @param ast a {@link KeyAst} object
     * @param <T> parse tree type
     * @return the {@link ParserRuleContext} inside the given ast object.
     */
    public static <T extends ParserRuleContext> @NonNull T getParseRuleContext(
            @NonNull KeyAst<T> ast) {
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
    public static @NonNull ChoiceInformation getChoices(@NonNull List<KeyAst.File> ctxs) {
        ChoiceInformation ci = new ChoiceInformation();
        ChoiceFinder finder = new ChoiceFinder(ci);
        ctxs.forEach(it -> it.accept(finder));
        return ci;
    }

    private static KeYParser createParser(TokenSource lexer) {
        KeYParser p = new KeYParser(new CommonTokenStream(lexer));
        p.removeErrorListeners();
        p.addErrorListener(p.getErrorReporter());
        return p;
    }


    private static KeYParser createParser(CharStream stream) {
        return createParser(createLexer(stream));
    }

    public static KeYLexer createLexer(Path file) throws IOException {
        return createLexer(CharStreams.fromPath(file));
    }

    public static KeYLexer createLexer(CharStream stream) {
        return new KeYLexer(stream);
    }

    public static @NonNull KeYLexer createLexer(@NonNull PositionedString ps) {
        var position = ps.getLocation().getPosition();
        var uri = ps.getLocation().fileUri().toString();

        CharStream result = CharStreams.fromString(ps.text, uri);
        var lexer = createLexer(result);
        lexer.getInterpreter().setCharPositionInLine(position.column());
        lexer.getInterpreter().setLine(position.line());
        return lexer;
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
        p.removeErrorListeners();
        p.setErrorHandler(new BailErrorStrategy());
        KeYParser.FileContext ctx;
        try {
            ctx = p.file();
        } catch (ParseCancellationException ex) {
            LOGGER.warn("SLL was not enough");
            stream.seek(0);
            p = createParser(stream);
            p.setErrorHandler(new BailErrorStrategy());
            ctx = p.file();
            if (p.getErrorReporter().hasErrors()) {
                throw ex;
            }
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

    public static KeyAst.ProofScript parseScript(PositionedString ps) {
        var rp = createParser(createLexer(ps));
        KeyAst.ProofScript ast = new KeyAst.ProofScript(rp.proofScript());
        rp.getErrorReporter().throwException(ps.text.split("\n"));
        return ast;
    }

    public static KeyAst.ProofScript parseScript(Path file) throws IOException {
        return parseScript(CharStreams.fromPath(file));
    }

    public static KeyAst.ProofScript parseScript(CharStream stream) {
        var rp = createParser(stream);
        final var ctx = rp.proofScriptEOF().proofScript();
        rp.getErrorReporter().throwException();
        return new KeyAst.ProofScript(ctx);
    }

    public static KeyAst.ProofScript parseScript(String text) {
        return parseScript(CharStreams.fromString(text));
    }

    /**
     * Translate a given context of a {@code string_value} grammar rule into a the literal value. In
     * particular it truncates, and substitutes quote escapes {@code \"}.
     *
     * @param ctx non-null context
     * @return non-null string
     */
    public static @NonNull String getValueDocumentation(
            KeYParser.@NonNull String_valueContext ctx) {
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

    public static @org.jspecify.annotations.Nullable String getValueDocumentation(
            @org.jspecify.annotations.Nullable TerminalNode docComment) {
        if (docComment == null) {
            return null;
        }
        String value = docComment.getText();
        return value.substring(3, value.length() - 2);// remove leading "/*!" and trailing "*/"
    }

    public static KeyAst.Taclet parseTaclet(String source) {
        return parseTaclet(CharStreams.fromString(source));
    }

    public static KeyAst.Taclet parseTaclet(CharStream source) {
        KeYParser p = createParser(source);
        var term = p.taclet();
        p.getErrorReporter().throwException();
        return new KeyAst.Taclet(term);
    }

    // region configuration

    /**
     * Parses the configuration determined by the given {@code file}.
     * A configuration corresponds to the grammar rule {@code cfile} in the {@code KeYParser.g4}.
     *
     * @param file non-null {@link Path} object
     * @return monad that encapsluate the ParserRuleContext
     * @throws IOException if the file is not found or not readable.
     * @throws BuildingException if the file is syntactical broken.
     */
    public static KeyAst.ConfigurationFile parseConfigurationFile(Path file) throws IOException {
        return parseConfigurationFile(CharStreams.fromPath(file));
    }

    /**
     * @param file non-null file to read as configuration
     * @throws IOException if the file is not found or not readable.
     * @see #parseConfigurationFile(Path)
     */
    public static KeyAst.ConfigurationFile parseConfigurationFile(File file) throws IOException {
        return parseConfigurationFile(file.toPath());
    }

    /**
     * Parses the configuration determined by the given {@code stream}.
     * A configuration corresponds to the grammar rule {@code cfile} in the {@code KeYParser.g4}.
     *
     * @param stream non-null {@link CharStream} object
     * @return monad that encapsluate the ParserRuleContext
     * @throws BuildingException if the file is syntactical broken.
     */
    public static KeyAst.ConfigurationFile parseConfigurationFile(CharStream stream) {
        KeYParser p = createParser(stream);
        var ctx = p.cfile();
        p.getErrorReporter().throwException();
        return new KeyAst.ConfigurationFile(ctx);
    }

    /**
     * Parses the configuration determined by the given {@code stream}.
     * A configuration corresponds to the grammar rule {@code cfile} in the {@code KeYParser.g4}.
     *
     * @param input non-null {@link CharStream} object
     * @return a configuration object with the data deserialize from the given file
     * @throws BuildingException if the file is syntactical broken.
     */
    public static Configuration readConfigurationFile(CharStream input) {
        return parseConfigurationFile(input).asConfiguration();
    }

    /**
     * @throws IOException if the file is not found or not readable.
     * @see #readConfigurationFile(CharStream)
     */
    public static Configuration readConfigurationFile(Path file) throws IOException {
        return readConfigurationFile(CharStreams.fromPath(file));
    }

    /**
     * @throws IOException if the file is not found or not readable.
     * @see #readConfigurationFile(CharStream)
     */
    public static Configuration readConfigurationFile(File file) throws IOException {
        return readConfigurationFile(file.toPath());
    }

    public static Configuration getConfiguration(KeYParser.TableContext ctx) {
        final var cfg = new ConfigurationBuilder();
        return cfg.visitTable(ctx);
    }
    // endregion
}

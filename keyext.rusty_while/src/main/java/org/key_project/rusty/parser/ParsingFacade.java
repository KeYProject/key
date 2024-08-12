/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.parser;

import java.io.BufferedInputStream;
import java.io.File;
import java.io.IOException;
import java.net.URL;
import java.nio.channels.Channels;
import java.nio.channels.ReadableByteChannel;
import java.nio.charset.Charset;
import java.nio.charset.CodingErrorAction;
import java.nio.file.Path;

import org.key_project.rusty.settings.Configuration;

import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.atn.PredictionMode;
import org.antlr.v4.runtime.misc.ParseCancellationException;

public final class ParsingFacade {
    private ParsingFacade() {
    }

    private static KeYRustyParser createParser(CharStream stream) {
        KeYRustyParser p = new KeYRustyParser(new CommonTokenStream(createLexer(stream)));
        // p.removeErrorListeners();
        // p.addErrorListener(p.getErrorReporter());
        return p;
    }

    public static KeYRustyLexer createLexer(Path file) throws IOException {
        return createLexer(CharStreams.fromPath(file));
    }

    public static KeYRustyLexer createLexer(CharStream stream) {
        return new KeYRustyLexer(stream);
    }

    public static KeYAst.File parseFile(URL url) throws IOException {
        long start = System.currentTimeMillis();
        try (BufferedInputStream is = new BufferedInputStream(url.openStream());
                ReadableByteChannel channel = Channels.newChannel(is)) {
            CodePointCharStream stream = CharStreams.fromChannel(channel, Charset.defaultCharset(),
                4096, CodingErrorAction.REPLACE, url.toString(), -1);
            return parseFile(stream);
        } finally {
            long stop = System.currentTimeMillis();
        }
    }

    public static KeYAst.File parseFile(Path file) throws IOException {
        return parseFile(CharStreams.fromPath(file));
    }

    public static KeYAst.File parseFile(File file) throws IOException {
        return parseFile(file.toPath());
    }

    public static KeYAst.File parseFile(CharStream stream) {
        KeYRustyParser p = createParser(stream);

        p.getInterpreter().setPredictionMode(PredictionMode.SLL);
        // p.removeErrorListeners();
        // p.setErrorHandler(new BailErrorStrategy());
        KeYRustyParser.FileContext ctx;
        try {
            ctx = p.file();
        } catch (ParseCancellationException ex) {
            stream.seek(0);
            p = createParser(stream);
            // p.setErrorHandler(new BailErrorStrategy());
            ctx = p.file();
            // if (p.getErrorReporter().hasErrors()) {
            // throw ex;
            // }
        }

        // p.getErrorReporter().throwException();
        return new KeYAst.File(ctx);
    }

    public static KeYAst.Term parseExpression(CharStream stream) {
        KeYRustyParser p = createParser(stream);
        KeYRustyParser.TermContext term = p.termEOF().term();
        // p.getErrorReporter().throwException();
        return new KeYAst.Term(term);
    }

    public static KeYAst.Seq parseSequent(CharStream stream) {
        KeYRustyParser p = createParser(stream);
        var seq = new KeYAst.Seq(p.seqEOF().seq());
        // p.getErrorReporter().throwException();
        return seq;
    }

    /**
     * Parses the configuration determined by the given {@code file}.
     * A configuration corresponds to the grammar rule {@code cfile} in the {@code KeYParser.g4}.
     *
     * @param file non-null {@link Path} object
     * @return monad that encapsluate the ParserRuleContext
     * @throws IOException if the file is not found or not readable.
     * @throws BuildingException if the file is syntactical broken.
     */
    public static KeYAst.ConfigurationFile parseConfigurationFile(Path file) throws IOException {
        return parseConfigurationFile(CharStreams.fromPath(file));
    }

    /**
     * Parses the configuration determined by the given {@code stream}.
     * A configuration corresponds to the grammar rule {@code cfile} in the {@code KeYParser.g4}.
     *
     * @param stream non-null {@link CharStream} object
     * @return monad that encapsluate the ParserRuleContext
     * @throws BuildingException if the file is syntactical broken.
     */
    public static KeYAst.ConfigurationFile parseConfigurationFile(CharStream stream) {
        KeYRustyParser p = createParser(stream);
        var ctx = p.cfile();
        // p.getErrorReporter().throwException();
        return new KeYAst.ConfigurationFile(ctx);
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
     * @see #readConfigurationFile(CharStream)
     * @throws IOException if the file is not found or not readable.
     */
    public static Configuration readConfigurationFile(Path file) throws IOException {
        return readConfigurationFile(CharStreams.fromPath(file));
    }

    /**
     * @see #readConfigurationFile(CharStream)
     * @throws IOException if the file is not found or not readable.
     */
    public static Configuration readConfigurationFile(File file) throws IOException {
        return readConfigurationFile(file.toPath());
    }

    public static Configuration getConfiguration(KeYRustyParser.TableContext ctx) {
        final var cfg = new ConfigurationBuilder();
        return cfg.visitTable(ctx);
    }
}

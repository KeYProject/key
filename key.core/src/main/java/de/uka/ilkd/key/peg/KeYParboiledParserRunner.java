/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg;

import de.uka.ilkd.key.peg.ast.File;
import de.uka.ilkd.key.peg.ast.Taclet;
import de.uka.ilkd.key.peg.ast.Term;
import org.checkerframework.checker.nullness.qual.MonotonicNonNull;
import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import org.parboiled.Parboiled;
import org.parboiled.errors.ParseError;
import org.parboiled.parserunners.ReportingParseRunner;
import org.parboiled.support.ParsingResult;

import java.io.IOException;
import java.nio.charset.Charset;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;

/**
 * Runner class for the PEG-based KeY parser using parboiled-java.
 * Provides a convenient API for parsing KeY specification files.
 *
 * @author Cline
 * @version 1.0
 */
@NullMarked
public class KeYParboiledParserRunner {

    private final KeYParboiledParser parser;

    public KeYParboiledParserRunner() {
        this.parser = Parboiled.createParser(KeYParboiledParser.class);
    }

    /**
     * Parse a KeY specification file from a Path.
     *
     * @param path The path to the file to parse
     * @return The parsed File AST node
     * @throws IOException if the file cannot be read
     * @throws RuntimeException if parsing fails
     */
    public @Nullable File parseFile(Path path) throws IOException {
        String content = Files.readString(path, Charset.defaultCharset());
        return parseString(content, path.toString());
    }

    /**
     * Parse a KeY specification from a String.
     *
     * @param content The content to parse
     * @return The parsed File AST node
     * @throws RuntimeException if parsing fails
     */
    public @Nullable File parseString(String content) {
        return parseString(content, "<string>");
    }

    /**
     * Parse a KeY specification from a String with a source name.
     *
     * @param content The content to parse
     * @param sourceName The name of the source (for error reporting)
     * @return The parsed File AST node
     * @throws RuntimeException if parsing fails
     */
    public @Nullable File parseString(String content, String sourceName) {
        ParsingResult<Object> result = new ReportingParseRunner<>(parser.File())
            .run(content);

        if (!result.matched) {
            throw new ParseException(
                "Failed to parse input: " + result.parseErrors,
                result.parseErrors
            );
        }

        // Extract the result from the value stack
        if (result.valueStack != null && !result.valueStack.isEmpty()) {
            Object top = result.valueStack.peek();
            if (top instanceof File) {
                return (File) top;
            }
        }

        throw new ParseException("Parsing succeeded but no AST was produced", result.parseErrors);
    }

    /**
     * Parse a term expression from a String.
     *
     * @param content The term content to parse
     * @return The parsed Term AST node
     * @throws RuntimeException if parsing fails
     */
    public @Nullable Term parseTerm(String content) {
        var result = new ReportingParseRunner<>(parser.Term())
            .run(content);

        if (!result.matched) {
            throw new ParseException(
                "Failed to parse term: " + result.parseErrors,
                result.parseErrors
            );
        }

        if (result.valueStack != null && !result.valueStack.isEmpty()) {
            Object top = result.valueStack.peek();
            if (top instanceof Term) {
                return (Term) top;
            }
        }

        throw new ParseException("Term parsing succeeded but no AST was produced", result.parseErrors);
    }

    /**
     * Parse a taclet from a String.
     *
     * @param content The taclet content to parse
     * @return The parsed Taclet AST node
     * @throws RuntimeException if parsing fails
     */
    public @Nullable Taclet parseTaclet(String content) {
        ParsingResult<Object> result = new ReportingParseRunner<>(parser.Taclet())
            .run(content);

        if (!result.matched) {
            throw new ParseException(
                "Failed to parse taclet: " + result.parseErrors,
                result.parseErrors
            );
        }

        if (result.valueStack != null && !result.valueStack.isEmpty()) {
            Object top = result.valueStack.peek();
            if (top instanceof Taclet) {
                return (Taclet) top;
            }
        }

        throw new ParseException("Taclet parsing succeeded but no AST was produced", result.parseErrors);
    }

    /**
     * Parse a configuration file from a String.
     *
     * @param content The configuration content to parse
     * @return A dummy result (configuration parsing is supported)
     * @throws RuntimeException if parsing fails
     */
    public boolean parseConfiguration(String content) {
        ParsingResult<Object> result = new ReportingParseRunner<>(parser.CFile())
            .run(content);

        if (!result.matched) {
            throw new ParseException(
                "Failed to parse configuration: " + result.parseErrors,
                result.parseErrors
            );
        }

        return true;
    }

    /**
     * Get the underlying parser instance for advanced usage.
     *
     * @return The KeYParboiledParser instance
     */
    public KeYParboiledParser getParser() {
        return parser;
    }

    /**
     * Exception thrown when parsing fails.
     */
    public static class ParseException extends RuntimeException {
        List<ParseError> parseErrors;
        public ParseException(String message, @MonotonicNonNull List<ParseError> parseError) {
            super(message);
            this.parseErrors = parseError;
        }

        public List<ParseError> getParseError() {
            return parseErrors;
        }
    }
}
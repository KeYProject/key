/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.util.parsing;

import java.net.URI;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.function.Supplier;
import java.util.stream.Collectors;

import de.uka.ilkd.key.util.ExceptionTools;

import org.key_project.util.java.StringUtil;
import org.key_project.util.parsing.HasLocation;
import org.key_project.util.parsing.Location;
import org.key_project.util.parsing.Position;
import org.key_project.util.parsing.SourceNames;

import org.antlr.v4.runtime.*;
import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * An ANTLR4 error listener that stores the errors internally. You can disable the additional
 * printing of message on the logger {@link #logger} flag.
 * <p>
 * It supports beautiful error message via {@link SyntaxError#getBeatifulErrorMessage(String[])}.
 *
 * @author Alexander Weigl
 * @version 1 (13.09.19)
 */
public class SyntaxErrorReporter extends BaseErrorListener {
    private final List<SyntaxError> errors = new ArrayList<>();
    /**
     * if true, exception is thrown directly when an error is hit
     */
    private final boolean throwDirect;

    private final @Nullable Logger logger;

    public SyntaxErrorReporter(@Nullable Logger logger, boolean throwDirect) {
        this.logger = logger;
        this.throwDirect = throwDirect;
    }

    public SyntaxErrorReporter(@Nullable Class<?> loggerCategory) {
        this(loggerCategory, false);
    }

    public SyntaxErrorReporter(@Nullable Class<?> loggerCategory, boolean throwDirect) {
        this(loggerCategory != null ? LoggerFactory.getLogger(loggerCategory) : null, throwDirect);
    }

    @Override
    public void syntaxError(Recognizer<?, ?> recognizer, @Nullable Object offendingSymbol, int line,
            int charPositionInLine, String msg, RecognitionException e) {

        Parser parser = (Parser) recognizer;
        String stack = String.join(", ", parser.getRuleInvocationStack());
        Token tok = (Token) offendingSymbol;
        if (tok == null) {
            throw new IllegalArgumentException(
                "offendedSymbol is null. Use SyntaxErrorReporter only in Parsers");
        }
        // Replace ANTLR's terse default messages (e.g. "mismatched input ';' expecting ...") with a
        // concise, human-readable description that names the expected token(s) and what was found.
        if (e instanceof InputMismatchException ime) {
            msg = ExceptionTools.describeSyntaxError(parser.getVocabulary(), tok,
                e.getExpectedTokens());
            // For a missing closing/terminating token, point at the insertion point just after the
            // preceding token (where the missing token belongs) rather than the next, unexpected
            // token - matching the single-error path. The recovery parser's LL prediction yields a
            // broad expected set, so accept a closing token being among the expected ones.
            Position ip = ExceptionTools.insertionPointFor(ime, false);
            if (ip != null) {
                line = ip.line();
                charPositionInLine = ip.column() - 1; // SyntaxError stores a 0-based column
            }
        }
        SyntaxError se = new SyntaxError(recognizer, line, tok, charPositionInLine, msg,
            SourceNames.getURIFromTokenSource(tok.getTokenSource()), stack);

        if (logger != null) {
            logger.warn("[syntax-error] {}:{}:{}: {} {} ({})", se.source, line, charPositionInLine,
                msg, tok, stack);
        }
        errors.add(se);

        if (throwDirect) {
            throwException();
        }
    }

    /**
     * Returns true, iff syntax errors were discovered by this listener.
     */
    public boolean hasErrors() {
        return !errors.isEmpty();
    }

    /**
     * @return the number of syntax errors discovered by this listener
     */
    public int errorCount() {
        return errors.size();
    }

    /**
     * Throws an exception if an error has occured.
     *
     * @see #hasErrors()
     */
    public void throwException() {
        if (hasErrors()) {
            throw new ParserException("", errors);
        }
    }


    /**
     * Throws an exception if an error has occured, like {@link #throwException()}, but with an
     * beautiful exception message based on input {@code lines}.
     *
     * @see #hasErrors()
     */
    public void throwException(String[] lines) {
        if (hasErrors()) {
            String msg = errors.stream().map(it -> it.getBeatifulErrorMessage(lines))
                    .collect(Collectors.joining("\n--- \n"));
            throw new ParserException(msg, Collections.unmodifiableList(errors));
        }
    }

    /**
     * Throws an exception if an error has occured, like {@link #throwException()}, but with an
     * beautiful exception message based on input {@code lines}.
     *
     * @see #hasErrors()
     */
    public void throwException(Supplier<String[]> lines) {
        if (hasErrors()) {
            throwException(lines.get());
        }
    }

    /**
     * This class represents an ANTLR4 error message. It captures every information needed to
     * identify the erroneous position in the input and parser (grammar rule stack). Also supports a
     * human-readable printing.
     */
    public static class SyntaxError {
        final Recognizer<?, ?> recognizer;
        final int line;
        final Token offendingSymbol;
        final int charPositionInLine;
        final String msg;
        final URI source;
        final String stack;

        public SyntaxError(Recognizer<?, ?> recognizer, int line, Token offendingSymbol,
                int charPositionInLine, String msg, URI source, String stack) {
            this.recognizer = recognizer;
            this.line = line;
            this.offendingSymbol = offendingSymbol;
            this.charPositionInLine = charPositionInLine;
            this.msg = msg;
            this.source = source;
            this.stack = stack;
        }

        public String getBeatifulErrorMessage(String[] lines) {
            return ("syntax-error in " + positionAsUrl() + "\n" + msg + "\n" + showInInput(lines)
                + "\n");
        }

        public String showInInput(String[] lines) {
            String line;
            try {
                line = lines[this.line];
            } catch (ArrayIndexOutOfBoundsException e) {
                line = "";
            }
            return line + "\n" + StringUtil.repeat(" ", (charPositionInLine - 1))
                + StringUtil.repeat("^", (offendingSymbol.getText().length()));
        }

        public String positionAsUrl() {
            return String.format("file://source:%d", line);
        }

        /**
         * @return the (already humanized, for an InputMismatch) error message of this single error
         */
        public String getMessage() {
            return msg;
        }

        /**
         * @return the source location of this error (1-based line and column)
         */
        public Location getLocation() {
            // charPositionInLine is 0-based
            return new Location(source, Position.fromOneZeroBased(line, charPositionInLine));
        }
    }

    public static class ParserException extends RuntimeException implements HasLocation {
        private final List<SyntaxError> errors;
        private final Location location;

        public ParserException(String msg, List<SyntaxError> errors) {
            super(msg);
            this.errors = errors;
            if (errors.isEmpty()) {
                location = Location.UNDEFINED;
            } else {
                SyntaxError e = errors.get(0);
                // e.charPositionInLine is 0 based!
                location =
                    new Location(e.source, Position.fromOneZeroBased(e.line, e.charPositionInLine));
            }
        }

        public String print(String[] lines, CharSequence delimter) {
            return errors.stream().map(it -> it.getBeatifulErrorMessage(lines))
                    .collect(Collectors.joining(delimter));
        }


        @Override
        public String getMessage() {
            StringBuilder s = new StringBuilder();
            for (SyntaxError error : errors) {
                s.append("line ").append(error.line).append(":").append(error.charPositionInLine)
                        .append(" ").append(error.msg).append("\n");
            }
            return s.toString();
        }

        @Override
        public @NonNull Location getLocation() {
            return location;
        }

        /**
         * @return the individual syntax errors, in the order they were encountered
         */
        public List<SyntaxError> getErrors() {
            return Collections.unmodifiableList(errors);
        }
    }
}

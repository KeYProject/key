/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.util.parsing;

import java.net.MalformedURLException;
import java.net.URI;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.function.Supplier;
import java.util.stream.Collectors;
import javax.annotation.Nullable;

import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.util.MiscTools;

import org.key_project.util.java.StringUtil;

import org.antlr.v4.runtime.*;
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

    private final Logger logger;

    public SyntaxErrorReporter(Logger logger, boolean throwDirect) {
        this.logger = logger;
        this.throwDirect = throwDirect;
    }

    public SyntaxErrorReporter(Class<?> loggerCategory) {
        this(loggerCategory, false);
    }

    public SyntaxErrorReporter(Class<?> loggerCategory, boolean throwDirect) {
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
        SyntaxError se = new SyntaxError(recognizer, line, tok, charPositionInLine, msg,
            MiscTools.getURIFromTokenSource(tok.getTokenSource()), stack);

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
     * Throws an exception if an error has occured.
     *
     * @throws de.uka.ilkd.key.parser.proofjava.ParseException
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
     * @throws de.uka.ilkd.key.parser.proofjava.ParseException
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
     * @throws de.uka.ilkd.key.parser.proofjava.ParseException
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
            String line = lines[this.line];
            return line + "\n" + StringUtil.repeat(" ", (charPositionInLine - 1))
                + StringUtil.repeat("^", (offendingSymbol.getText().length()));
        }

        public String positionAsUrl() {
            return String.format("file://source:%d", line);
        }
    }

    public static class ParserException extends RuntimeException implements HasLocation {
        private final List<SyntaxError> errors;

        public ParserException(String msg, List<SyntaxError> errors) {
            super(msg);
            this.errors = errors;
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
        public Location getLocation() throws MalformedURLException {
            if (!errors.isEmpty()) {
                SyntaxError e = errors.get(0);
                // e.charPositionInLine is 0 based!
                return new Location(e.source,
                    Position.fromOneZeroBased(e.line, e.charPositionInLine));
            }
            return null;
        }
    }
}

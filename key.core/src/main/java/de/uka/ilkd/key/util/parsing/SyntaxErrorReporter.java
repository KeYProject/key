/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.util.parsing;

import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.util.MiscTools;
import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.misc.ParseCancellationException;
import org.jspecify.annotations.Nullable;
import org.key_project.util.java.StringUtil;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.net.MalformedURLException;
import java.net.URI;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.function.Supplier;
import java.util.stream.Collectors;

/**
 * An ANTLR4 error listener that stores the errors internally. You can disable the additional
 * printing of message on the logger {@link #logger} flag.
 * <p>
 * It supports beautiful error message via {@link SyntaxError#getBeatifulErrorMessage(String[])}.
 *
 * @author Alexander Weigl
 * @version 1 (13.09.19)
 */
public class SyntaxErrorReporter extends BaseErrorListener implements ANTLRErrorStrategy {
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

    public SyntaxErrorReporter join(SyntaxErrorReporter other) {
        var newOne = new SyntaxErrorReporter(logger, throwDirect);
        newOne.errors.addAll(errors);
        newOne.errors.addAll(other.errors);
        return newOne;
    }

    public List<SyntaxError> getErrors() {
        return errors;
    }


    final BailErrorStrategy bailoutStrategy = new BailErrorStrategy();

    @Override
    public void reset(Parser recognizer) {
        bailoutStrategy.reset(recognizer);
    }

    @Override
    public Token recoverInline(Parser recognizer) throws RecognitionException {
        InputMismatchException e = new InputMismatchException(recognizer);
        for (ParserRuleContext context = recognizer.getContext(); context != null; context = context.getParent()) {
            context.exception = e;
        }
        var tok = e.getOffendingToken();

        var message = "I got offended by the token '%s'. Expected tokens are: %s".formatted(tok,
                e.getExpectedTokens().toString(recognizer.getVocabulary()));

        syntaxError(recognizer, e.getOffendingToken(),
                tok.getLine(), tok.getCharPositionInLine(), message, e);
        throw new ParseCancellationException(e);
    }

    @Override
    public void recover(Parser recognizer, RecognitionException e) throws RecognitionException {
        for (ParserRuleContext context = recognizer.getContext(); context != null; context = context.getParent()) {
            context.exception = e;
        }
        var tok = e.getOffendingToken();
        final var parseCancellationException = new ParseCancellationException(e);

        var message = "I got offended by the token '%s'. Expected tokens are: %s".formatted(tok,
                e.getExpectedTokens().toString(recognizer.getVocabulary()));

        syntaxError(recognizer, e.getOffendingToken(),
                tok.getLine(), tok.getCharPositionInLine(), message, e);

        throw parseCancellationException;
    }

    @Override
    public void sync(Parser recognizer) throws RecognitionException {
        bailoutStrategy.sync(recognizer);
    }

    @Override
    public boolean inErrorRecoveryMode(Parser recognizer) {
        return bailoutStrategy.inErrorRecoveryMode(recognizer);
    }

    @Override
    public void reportMatch(Parser recognizer) {
        bailoutStrategy.reportMatch(recognizer);
    }

    @Override
    public void reportError(Parser recognizer, RecognitionException e) {
        bailoutStrategy.reportError(recognizer, e);
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

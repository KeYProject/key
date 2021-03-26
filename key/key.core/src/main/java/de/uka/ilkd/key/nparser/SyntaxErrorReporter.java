package de.uka.ilkd.key.nparser;

import com.google.common.base.Strings;
import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.util.MiscTools;
import org.antlr.v4.runtime.*;
import org.jetbrains.annotations.Nullable;

import java.net.MalformedURLException;
import java.net.URL;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.function.Supplier;
import java.util.stream.Collectors;

/**
 * An ANTLR4 error listener that stores the errors internally.
 * You can disable the additional  printing of message on the console {@link #print} flag.
 * <p>
 * It supports beautiful error message via {@link SyntaxError#getBeatifulErrorMessage(String[])}.
 *
 * @author Alexander Weigl
 * @version 1 (13.09.19)
 */
public class SyntaxErrorReporter extends BaseErrorListener {
    private final List<SyntaxError> errors = new ArrayList<>();
    private boolean print = true;

    @Override
    public void syntaxError(Recognizer<?, ?> recognizer, @Nullable Object offendingSymbol,
                            int line, int charPositionInLine, String msg, RecognitionException e) {

        Parser parser = (Parser) recognizer;
        String stack = String.join(", ", parser.getRuleInvocationStack());
        Token tok = (Token) offendingSymbol;
        if (tok == null) {
            throw new IllegalArgumentException("offendedSymbol is null. Use SyntaxErrorReporter only in Parsers");
        }
        SyntaxError se = new SyntaxError(
                recognizer,
                line,
                tok,
                charPositionInLine,
                msg, tok.getTokenSource().getSourceName(), stack);

        if (print) {
            System.err.printf("[syntax-error] %s:%d:%d: %s %s (%s)%n", se.source, line, charPositionInLine, msg, tok, stack);
        }
        errors.add(se);
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
        if (hasErrors())
            throw new ParserException("", errors);
    }


    /**
     * Throws an exception if an error has occured, like {@link #throwException()},
     * but with an beautiful exception message based on input {@code lines}.
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
     * Throws an exception if an error has occured, like {@link #throwException()},
     * but with an beautiful exception message based on input {@code lines}.
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
     * This class represents an ANTLR4 error message. It captures every information needed to identify
     * the erroneous position in the input and parser (grammar rule stack). Also supports a human-readable printing.
     */
    public static class SyntaxError {
        final Recognizer<?, ?> recognizer;
        final int line;
        final Token offendingSymbol;
        final int charPositionInLine;
        final String msg;
        final String source;
        final String stack;

        public SyntaxError(Recognizer<?, ?> recognizer, int line, Token offendingSymbol, int charPositionInLine, String msg, String source, String stack) {
            this.recognizer = recognizer;
            this.line = line;
            this.offendingSymbol = offendingSymbol;
            this.charPositionInLine = charPositionInLine;
            this.msg = msg;
            this.source = source;
            this.stack = stack;
        }

        public String getBeatifulErrorMessage(String[] lines) {
            return ("syntax-error in " + positionAsUrl() + "\n"
                    + msg + "\n" + showInInput(lines) + "\n");
        }

        public String showInInput(String[] lines) {
            String line = lines[this.line];
            return line +
                    "\n" +
                    Strings.repeat(" ", (charPositionInLine - 1)) +
                    Strings.repeat("^", (offendingSymbol.getText().length()));
        }

        public String positionAsUrl() {
            return String.format("file://source:%d", line);
        }
    }

    public static class ParserException extends RuntimeException {
        private final List<SyntaxError> errors;

        public ParserException(String msg, List<SyntaxError> errors) {
            super(msg);
            this.errors = errors;
        }

        public String print(String[] lines, CharSequence delimter) {
            return errors.stream()
                    .map(it -> it.getBeatifulErrorMessage(lines))
                    .collect(Collectors.joining(delimter));
        }


        @Override
        public String getMessage() {
            StringBuilder s = new StringBuilder();
            for (SyntaxError error : errors) {
                s.append("line ").append(error.line).append(":").append(error.charPositionInLine).append(" ").append(error.msg)
                        .append("\n");
            }
            return s.toString();
        }

        public Location getLocation() throws MalformedURLException {
            if (!errors.isEmpty()) {
                SyntaxError e = errors.get(0);
                return new Location(MiscTools.parseURL(e.source), e.line, e.charPositionInLine);
            }
            return null;
        }
    }
}
package de.uka.ilkd.key.nparser;

import com.google.common.base.Strings;
import org.antlr.v4.runtime.*;
import org.jetbrains.annotations.Nullable;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.function.Supplier;
import java.util.stream.Collectors;

/**
 * @author Alexander Weigl
 * @version 1 (13.09.19)
 */
public class SyntaxErrorReporter extends BaseErrorListener {
    private final List<SyntaxError> errors = new ArrayList<SyntaxError>();
    private boolean isPrint = true;

    @Override
    public void syntaxError(@Nullable Recognizer<?, ?> recognizer, @Nullable Object offendingSymbol,
                            int line, int charPositionInLine, String msg, RecognitionException e) {

        var parser = (Parser) recognizer;
        var stack = String.join(", ", parser.getRuleInvocationStack());
        var tok = (Token) offendingSymbol;
        var se = new SyntaxError(
                recognizer,
                line,
                tok,
                charPositionInLine,
                msg, tok.getTokenSource().getSourceName(), stack);

        if (isPrint) {
            System.err.printf("[syntax-error] %s:%d:%d: %s %s (%s)%n", se.source, line, charPositionInLine, msg, tok, stack);
        }
        errors.add(se);
    }

    public Boolean hasErrors() {
        return !errors.isEmpty();
    }

    public void throwException() {
        if (hasErrors()) throw new ParserException("", errors);
    }


    public void throwException(String[] lines) {
        if (hasErrors()) {
            var msg = errors.stream().map(it -> it.getBeatifulErrorMessage(lines))
                    .collect(Collectors.joining("\n--- \n"));
            throw new ParserException(msg, Collections.unmodifiableList(errors));
        }
    }

    public void throwException(Supplier<String[]> lines) {
        if (hasErrors()) {
            throwException(lines.get());
        }
    }

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
            var line = lines[this.line];
            var sb = new StringBuilder();
            sb.append(line)
                    .append("\n")
                    .append(Strings.repeat(" ", (charPositionInLine - 1)))
                    .append(Strings.repeat("^", (offendingSymbol.getText().length())));
            return sb.toString();
        }

        public String positionAsUrl() {
            return String.format("file://source:%d", line);
        }
    }

    public static class ParserException extends RuntimeException {
        private final String msg;
        private final List<SyntaxError> errors;

        public ParserException(String msg, List<SyntaxError> errors) {
            this.msg = msg;
            this.errors = errors;
        }

        public String print(String[] lines, CharSequence delimter) {
            return errors.stream()
                    .map(it -> it.getBeatifulErrorMessage(lines))
                    .collect(Collectors.joining(delimter));
        }
    }
}
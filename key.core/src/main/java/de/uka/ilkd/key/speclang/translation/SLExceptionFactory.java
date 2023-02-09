package de.uka.ilkd.key.speclang.translation;

import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.speclang.PositionedString;
import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.Token;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.util.LinkedList;
import java.util.List;

import static java.text.MessageFormat.format;


/**
 * Factory for exception during parsing of specification languages.
 * <p>
 * This class produces exception with position information. For this, the class can be constructed
 * from antlr3.
 */
public class SLExceptionFactory {
    public static final Logger LOGGER = LoggerFactory.getLogger(SLExceptionFactory.class);

    private String fileName;
    private final int offsetLine, offsetColumn, offsetIndex;
    private int line;
    private int column;
    private int index;

    private List<PositionedString> warnings = new LinkedList<>();

    // -------------------------------------------------------------------------
    // constructors
    // -------------------------------------------------------------------------

    public SLExceptionFactory(String fileName, int line, int column, int index) {
        this.fileName = fileName;
        this.offsetColumn = column;
        this.offsetIndex = index;
        this.offsetLine = line;
        this.line = 0;
        this.column = 0;
    }

    public SLExceptionFactory updatePosition(ParserRuleContext context) {
        return updatePosition(context.start);
    }

    public SLExceptionFactory updatePosition(org.antlr.v4.runtime.Token start) {
        fileName = start.getTokenSource().getSourceName();
        index = start.getStartIndex();
        line = start.getLine();
        column = start.getCharPositionInLine();
        return this;
    }

    // -------------------------------------------------------------------------
    // internal methods
    // -------------------------------------------------------------------------
    private Position createAbsolutePosition(int relativeLine, int relativeColumn) {
        int absoluteLine = offsetLine + relativeLine - 1;
        int absoluteColumn = (relativeLine == 1 ? offsetColumn : 1) + relativeColumn - 1;
        return new Position(absoluteLine, absoluteColumn);
    }

    private Position createAbsolutePosition(final Position pos) {
        return this.createAbsolutePosition(pos.getLine(), pos.getColumn());
    }

    // -------------------------------------------------------------------------
    // public interface
    // -------------------------------------------------------------------------

    // region warnings

    /**
     * This is used for features without semantics such as labels or annotations.
     *
     * @author bruns
     * @since 1.7.2178
     */
    public void addIgnoreWarning(String feature) {
        String msg = feature + " is not supported and has been silently ignored.";
        addWarning(msg);
    }

    public void addIgnoreWarning(String feature, org.antlr.v4.runtime.Token t) {
        String msg = feature + " is not supported and has been silently ignored.";
        addWarning(msg, t);
    }

    public void raiseNotSupported(String feature) {
        addWarning(feature + " not supported");
    }

    /**
     * Used for features with semantics (currently) not supported in KeY/DL.
     */
    public void addUnderspecifiedWarning(String feature) {
        String msg = format(
            "{0} is not supported and translated to an underspecified term or formula.", feature);
        addWarning(msg);
    }

    public void addUnderspecifiedWarning(org.antlr.v4.runtime.Token t) {
        String msg =
            format("{0} is not supported and translated to an underspecified term or formula.",
                t.getText());
        addWarning(msg, t);
    }

    public void addDeprecatedWarning(String feature) {
        addWarning("deprecated syntax: " + feature);
    }

    public void addWarning(String msg) {
        LOGGER.debug("JML translator warning: " + msg);
        warnings.add(new PositionedString(msg, ""));
    }

    public void addWarning(String msg, org.antlr.v4.runtime.Token t) {
        LOGGER.debug("JML translator warning: " + msg);
        warnings.add(createPositionedString(msg, t));
    }

    public List<PositionedString> getWarnings() {
        return warnings;
    }
    // endregion

    public PositionedString createPositionedString(String msg, Token t) {
        return new PositionedString(msg, fileName,
            createAbsolutePosition(t.getLine(), t.getCharPositionInLine()));
    }

    /**
     * Creates a string with position information from the given relative position.
     *
     * @param text the {@link String}
     * @param pos the {@link Position}
     * @return <code>text</code> as {@link PositionedString} with absolute position in the current
     *         file
     */
    public PositionedString createPositionedString(final String text, final Position pos) {
        return new PositionedString(text, fileName, createAbsolutePosition(pos));
    }

    /**
     * Creates a string with the current absolute position information
     */
    public PositionedString createPositionedString(String text) {
        return new PositionedString(text, fileName, createAbsolutePosition(this.line, this.column));
    }


    /**
     * Creates an SLTranslationException with current absolute position information.
     */
    public SLTranslationException createException(String message) {
        return new SLTranslationException(message, fileName,
            createAbsolutePosition(this.line, this.column));
    }


    /**
     * Creates an SLTranslationException with the position information of the passed token.
     */
    public SLTranslationException createException(String message, Token t) {
        return new SLTranslationException(message, fileName,
            createAbsolutePosition(t.getLine(), t.getCharPositionInLine()));
    }

    /**
     * Creates an SLTranslationException with current absolute position information.
     */
    public SLTranslationException createException(String message, Throwable cause) {
        SLTranslationException result = createException(message);
        result.initCause(cause);
        return result;
    }

    public RuntimeException createException0(String s) {
        return new RuntimeException(createException(s));
    }

    public RuntimeException createException0(String s, Throwable t) {
        return new RuntimeException(createException(s, t));
    }

    public RuntimeException createException0(String s, Token t) {
        return new RuntimeException(createException(s, t));
    }

    public RuntimeException createException0(String s, Token t, Throwable cause) {
        return new RuntimeException(createException(s, t, cause));
    }

    /**
     * Creates an SLTranslationException with the position information of the passed token.
     *
     * @param cause the exception which causes the new exception to be created.
     */
    public SLTranslationException createException(String message, Token t, Throwable cause) {
        SLTranslationException result = createException(message, t);
        result.initCause(cause);
        return result;
    }
}

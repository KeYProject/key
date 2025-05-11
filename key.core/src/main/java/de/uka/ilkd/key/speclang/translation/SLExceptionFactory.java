/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang.translation;

import java.net.URI;
import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.speclang.PositionedString;
import de.uka.ilkd.key.util.MiscTools;

import org.antlr.v4.runtime.Parser;
import org.antlr.v4.runtime.Token;
import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import static java.text.MessageFormat.format;


/**
 * Factory for exception during parsing of specification languages.
 * <p>
 * This class produces exception with position information. For this, the class can be constructed
 * from antlr3.
 */
public class SLExceptionFactory {
    public static final Logger LOGGER = LoggerFactory.getLogger(SLExceptionFactory.class);

    private @Nullable URI fileName;
    private final int offsetLine, offsetColumn;
    /**
     * line, 1-based
     */
    private int line;
    /**
     * column, 0-based
     */
    private int column;

    private final List<PositionedString> warnings = new LinkedList<>();

    // -------------------------------------------------------------------------
    // constructors
    // -------------------------------------------------------------------------

    public SLExceptionFactory(@NonNull Parser parser, URI fileName, @NonNull Position offsetPos) {
        this.line = parser.getInputStream().LT(1).getLine();
        this.column = parser.getInputStream().LT(1).getCharPositionInLine();
        this.fileName = fileName;
        this.offsetColumn = offsetPos.column();
        this.offsetLine = offsetPos.line();
    }

    public SLExceptionFactory(URI fileName, int line, int column) {
        this.fileName = fileName;
        this.offsetColumn = column;
        this.offsetLine = line;
        this.line = 1;
        this.column = 0;
    }

    public @NonNull SLExceptionFactory updatePosition(@NonNull Token start) {
        fileName = MiscTools.getURIFromTokenSource(start.getTokenSource());
        line = start.getLine();
        column = start.getCharPositionInLine();
        return this;
    }

    // -------------------------------------------------------------------------
    // internal methods
    // -------------------------------------------------------------------------
    private @NonNull Location createAbsolutePosition(int relativeLine, int relativeColumn) {
        int absoluteLine = offsetLine + relativeLine - 1;
        int absoluteColumn = (relativeLine == 1 ? offsetColumn : 1) + relativeColumn;
        return new Location(fileName, Position.fromOneZeroBased(absoluteLine, absoluteColumn));
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

    public void addIgnoreWarning(String feature, @NonNull Token t) {
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

    public void addUnderspecifiedWarning(@NonNull Token t) {
        String msg =
            format("{0} is not supported and translated to an underspecified term or formula.",
                t.getText());
        addWarning(msg, t);
    }

    public void addDeprecatedWarning(String feature) {
        addWarning("deprecated syntax: " + feature);
    }

    public void addWarning(@NonNull String msg) {
        LOGGER.debug("JML translator warning: " + msg);
        warnings.add(new PositionedString(msg));
    }

    public void addWarning(@NonNull String msg, @NonNull Token t) {
        LOGGER.debug("JML translator warning: " + msg);
        warnings.add(createPositionedString(msg, t));
    }

    public @NonNull List<PositionedString> getWarnings() {
        return warnings;
    }
    // endregion

    public @NonNull PositionedString createPositionedString(@NonNull String msg, @NonNull Token t) {
        return new PositionedString(msg,
            createAbsolutePosition(t.getLine(), t.getCharPositionInLine()));
    }

    /**
     * Creates an SLTranslationException with current absolute position information.
     */
    public @NonNull SLTranslationException createException(String message) {
        return new SLTranslationException(message, createAbsolutePosition(this.line, this.column));
    }


    /**
     * Creates an SLTranslationException with the position information of the passed token.
     */
    public @NonNull SLTranslationException createException(String message, @NonNull Token t) {
        return new SLTranslationException(message,
            createAbsolutePosition(t.getLine(), t.getCharPositionInLine()));
    }

    /**
     * Creates an SLTranslationException with current absolute position information.
     */
    public @NonNull SLTranslationException createException(String message, Throwable cause) {
        SLTranslationException result = createException(message);
        result.initCause(cause);
        return result;
    }

    public @NonNull RuntimeException createException0(String s) {
        return new RuntimeException(createException(s));
    }

    public @NonNull RuntimeException createException0(String s, Throwable t) {
        return new RuntimeException(createException(s, t));
    }

    public @NonNull RuntimeException createException0(String s, @NonNull Token t) {
        return new RuntimeException(createException(s, t));
    }

    public @NonNull RuntimeException createException0(String s, @NonNull Token t, Throwable cause) {
        return new RuntimeException(createException(s, t, cause));
    }

    /**
     * Creates an SLTranslationException with the position information of the passed token.
     *
     * @param cause the exception which causes the new exception to be created.
     */
    public @NonNull SLTranslationException createException(String message, @NonNull Token t, Throwable cause) {
        SLTranslationException result = createException(message, t);
        result.initCause(cause);
        return result;
    }
}

/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.util.parsing;

/**
 * Thrown by the KeY lexer when the body of a modality (a schematic program) contains another
 * modality-opening keyword, which means the current modality's closing keyword
 * ({@code \endmodality} / {@code \>} / {@code \]}) is missing. It carries the position of the
 * <em>opening</em> of the unterminated modality so the error can be reported there (rather than at
 * the next, unrelated closing keyword the lexer would otherwise run on to). See issue #3867.
 *
 * <p>
 * This lives in {@code key.ncore} so the generated lexer can throw it; the position is turned into
 * a
 * proper {@code Location} by {@code ExceptionTools} in {@code key.core}.
 */
public class UnterminatedModalityException extends RuntimeException {
    private static final long serialVersionUID = 1L;

    /** 1-based line of the modality opening. */
    private final int line;
    /** 0-based column of the modality opening (ANTLR convention). */
    private final int charPositionInLine;
    private final String sourceName;

    public UnterminatedModalityException(String message, int line, int charPositionInLine,
            String sourceName) {
        super(message);
        this.line = line;
        this.charPositionInLine = charPositionInLine;
        this.sourceName = sourceName;
    }

    /** @return the 1-based line of the modality opening */
    public int getLine() {
        return line;
    }

    /** @return the 0-based column (ANTLR convention) of the modality opening */
    public int getCharPositionInLine() {
        return charPositionInLine;
    }

    /** @return the source name (file/URI string) reported by the lexer's input */
    public String getSourceName() {
        return sourceName;
    }
}

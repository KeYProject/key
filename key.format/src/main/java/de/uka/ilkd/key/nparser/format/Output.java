/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.nparser.format;

import de.uka.ilkd.key.nparser.KeYLexer;

import org.antlr.v4.runtime.Token;

/**
 * Output class for managing formatted output with indentation.
 * <p>
 * This class provides methods to manage and format output with proper
 * indentation and spacing. It supports adding tokens, characters, and
 * handling new lines and indentation levels.
 *
 * @author Julian Wiesler
 * @see ExpressionVisitor
 */
class Output {
    public static final int INDENT_STEP = 4;

    private final StringBuilder output = new StringBuilder();
    private int indentLevel = 0;
    private boolean isNewLine = true;
    private boolean spaceBeforeNextToken = false;

    /**
     * Generates a string of whitespaces indentation.
     *
     * @param count indentation level
     * @return string of empty spaces
     */
    static String getIndent(int count) {
        // Substrings use a shared buffer
        return " ".repeat(INDENT_STEP * count);
    }

    private void indent() {
        output.append(getIndent(indentLevel));
        this.isNewLine = false;
        this.spaceBeforeNextToken = false;
    }

    private void checkBeforeToken() {
        if (this.isNewLine) {
            indent();
        } else if (spaceBeforeNextToken) {
            output.append(' ');
            this.spaceBeforeNextToken = false;
        }
    }

    /**
     * Before the next token starts, a space will be inserted
     * Dual operation to {@link #noSpaceBeforeNext()}
     */
    public void spaceBeforeNext() {
        this.spaceBeforeNextToken = true;
    }

    /**
     * Before the next token starts, no space will be inserted.
     * Dual operation to {@link #spaceBeforeNextToken}
     */
    public void noSpaceBeforeNext() {
        this.spaceBeforeNextToken = false;
    }


    public void token(Token value) {
        checkBeforeToken();
        if (lastTokenId == KeYLexer.IDENT && value.getType() == KeYLexer.IDENT) {
            spaceBeforeNext();
        }
        output.append(value.getText());
        lastTokenId = value.getType();
    }

    /**
     * Add a token to the output. Respects whitespace before token.
     *
     * @param text a string value
     */
    public void token(String text) {
        checkBeforeToken();
        output.append(text);
        lastTokenId = 0;
    }

    private int lastTokenId;

    /**
     * Increases the indentation level.
     */
    public void enterIndent() {
        indentLevel++;
    }

    /**
     * Decreases the indentation level.
     */
    public void exitIndent() {
        if (indentLevel == 0) {
            throw new IllegalStateException("Unmatched closing RPAREN.");
        }
        indentLevel--;
    }

    /**
     * Returns true iff cursor stays on a fresh line.
     */
    public boolean isNewLine() {
        return isNewLine;
    }

    /**
     * Goes to a fresh line with current indentation.
     */
    public void assertNewLineAndIndent() {
        clearline();
        indent();
    }

    /**
     * Prints intendation if on necessary/on a fresh line.
     */
    public void assertIndented() {
        if (isNewLine) {
            indent();
        }
    }

    /**
     * Prints a new line.
     */
    public void newLine() {
        this.isNewLine = true;
        output.append('\n');
    }

    /**
     * Prints a newline if necessary.
     */
    public void clearline() {
        if (!this.isNewLine) {
            newLine();
        }
    }

    @Override
    public String toString() {
        return output.toString();
    }
}

/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.nparser.format;

class Output {
    public static final int INDENT_STEP = 4;
    private static final String INDENT_BUFFER = " ".repeat(100);

    private final StringBuilder output;
    private int indentLevel = 0;
    private boolean isNewLine = true;
    private boolean spaceBeforeNextToken = false;

    public static String getIndent(int count) {
        // Substrings use a shared buffer
        return INDENT_BUFFER.substring(0, INDENT_STEP * count);
    }

    public Output() {
        output = new StringBuilder();
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

    public void spaceBeforeNext() {
        this.spaceBeforeNextToken = true;
    }

    public void noSpaceBeforeNext() {
        this.spaceBeforeNextToken = false;
    }

    public void token(String value) {
        checkBeforeToken();
        output.append(value);
    }

    public void token(char value) {
        checkBeforeToken();
        output.append(value);
    }

    public void enterIndent() {
        indentLevel++;
    }

    public void exitIndent() {
        if (indentLevel == 0) {
            throw new IllegalStateException("Unmatched closing RPAREN.");
        }
        indentLevel--;
    }

    public boolean isNewLine() {
        return isNewLine;
    }

    public void assertNewLineAndIndent() {
        assertNewLine();
        indent();
    }

    public void assertIndented() {
        if (isNewLine) {
            indent();
        }
    }

    public void newLine() {
        this.isNewLine = true;
        output.append('\n');
    }

    public void assertNewLine() {
        if (!this.isNewLine) {
            newLine();
        }
    }

    @Override
    public String toString() {
        return output.toString();
    }
}

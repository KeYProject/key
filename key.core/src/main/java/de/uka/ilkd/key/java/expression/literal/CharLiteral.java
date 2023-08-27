/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.expression.literal;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.visitor.Visitor;

import org.key_project.util.ExtList;

/**
 * Char literal.
 *
 * @author <TT>Wolfram Pfeifer</TT>
 */
public class CharLiteral extends AbstractIntegerLiteral {

    /**
     * The actual char this CharLiteral represents.
     */
    private final char charVal;

    /**
     * Creates a new CharLiteral from the given char.
     *
     * @param charVal a char value.
     */
    public CharLiteral(char charVal) {
        this.charVal = charVal;
    }

    /**
     * Creates a new CharLiteral from the given String. Char literals can be given as described in
     * the Java 8 Language Specification: chars written directly (like 'a', '0', 'Z'), Java escape
     * chars (like '\n', '\r'), and octal Unicode escapes (like '\040'). Note that unicode escapes
     * in hexadecimal form are processed earlier and don't have to be handled here.
     *
     * Note that the char must be enclosed in single-quotes.
     *
     * @param children an ExtList with all children(comments). May contain: Comments
     * @param valueStr a string.
     */
    public CharLiteral(ExtList children, String valueStr) {
        super(children);
        this.charVal = parseFromString(valueStr);
    }

    /**
     * Creates a new CharLiteral from the given String. The String must be of the form
     * <code>'c'</code> (with c being an arbitrary char).
     *
     * @param valueStr a string.
     */
    public CharLiteral(String valueStr) {
        this.charVal = parseFromString(valueStr);
    }

    /**
     * Returns the decimal value of the char.
     *
     * @return the decimal value of the char as a BigInteger
     */
    public long getValue() {
        return charVal;
    }

    @Override
    public void visit(Visitor v) {
        v.performActionOnCharLiteral(this);
    }

    @Override
    public KeYJavaType getKeYJavaType(Services javaServ) {
        return javaServ.getJavaInfo().getKeYJavaType(PrimitiveType.JAVA_CHAR);
    }

    @Override
    public String toString() {
        // the actual char surrounded by single-quotes
        return "'" + charVal + "'";
    }

    @Override
    public String getValueString() {
        // the char value as a decimal number (without single-quotes)
        return String.valueOf((int) charVal);
    }

    /**
     * Parses the String and extracts the actual value of the literal. This method is able to parse
     * char literals as described in the Java 8 Language Specification: chars written directly (like
     * 'a', '0', 'Z'), Java escape chars (like '\n', '\r'), and octal Unicode escapes (like '\040').
     * Note that unicode escapes in hexadecimal form are processed earlier and don't have to be
     * handled by this method.
     *
     * This method does not check the length of the literal for validity.
     *
     * @param sourceStr the String containing the literal surrounded by single-quotes
     * @return the parsed value as a char
     * @throws NumberFormatException if the given String does not represent a syntactically valid
     *         character literal or the literal is not surrounded by single-quotes
     * @see <a href="https://docs.oracle.com/javase/specs/jls/se8/html/jls-3.html#jls-3.10.4">
     *      https://docs.oracle.com/javase/specs/jls/se8/html/jls-3.html#jls-3.10.4</a>
     */
    protected char parseFromString(final String sourceStr) {
        if (sourceStr.charAt(0) != '\'' || sourceStr.charAt(sourceStr.length() - 1) != '\'') {
            throw new NumberFormatException("Invalid char delimiters: " + sourceStr);
        }

        String valStr = sourceStr.substring(1, sourceStr.length() - 1);

        /*
         * There are three possible cases: 1. the char is written directly 2. Java escape like '\n'
         * 3. octal Unicode escape like '\040'
         */
        if (valStr.charAt(0) == '\\') {
            switch (valStr.charAt(1)) {
            case 'b':
                return '\b';
            case 't':
                return '\t';
            case 'n':
                return '\n';
            case 'f':
                return '\f';
            case 'r':
                return '\r';
            case '\"':
                return '\"';
            case '\'':
                return '\'';
            case '\\':
                return '\\';
            case '0':
            case '1':
            case '2':
            case '3':
            case '4':
            case '5':
            case '6':
            case '7':
                return (char) Integer.parseInt(valStr.substring(1), 8);
            case 'u':
                return (char) Integer.parseInt(valStr.substring(2), 16);
            default:
                throw new NumberFormatException("Invalid char: " + sourceStr);
            }
        } else {
            return valStr.charAt(0);
        }
    }
}

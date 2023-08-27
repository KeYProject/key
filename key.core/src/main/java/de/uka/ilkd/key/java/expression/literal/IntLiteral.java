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
 * Int literal.
 *
 * @author <TT>AutoDoc</TT>
 */

public class IntLiteral extends AbstractIntegerLiteral {

    /**
     * A constant holding the maximum valid value as if an int was interpreted unsigned:
     * 2<sup>32</sup>-1
     */
    private static final long MAX_UINT = 0xffffffffL;

    /**
     * Textual representation of the value as a decimal number.
     */
    private final String valueStr;

    /**
     * The actual value of the literal.
     */
    private final int value;

    /**
     * Creates a new IntLiteral representing the given int.
     *
     * @param value the int value represented by the literal
     */
    public IntLiteral(int value) {
        this.value = value;
        this.valueStr = (String.valueOf(value)).intern();
    }

    /**
     * Creates a new IntLiteral from the given String. The String is parsed and checked for range.
     * The input may be any String containing a literal as described by the Java 8 Language
     * Specification. This includes hexadecimal, decimal, octal, and binary literals as well as
     * literals containing underscores as separators. In addition, a preceding '-' sign is allowed.
     *
     * @param valStr the String that contains the literal
     * @throws NumberFormatException if the given String does not represent a syntactically valid
     *         literal or represents a value out of int range
     * @see <a href="http://docs.oracle.com/javase/specs/jls/se8/html/jls-3.html#jls-3.10.1">
     *      http://docs.oracle.com/javase/specs/jls/se8/html/jls-3.html#jls-3.10.1</a>
     */
    public IntLiteral(String valStr) {
        this.value = parseFromString(valStr);
        this.valueStr = Integer.toString(value).intern();
    }

    /**
     * Constructor for Recoder2KeY transformation.
     *
     * @param children the children of this AST element as KeY classes, may contain: Comments
     * @param valStr the value of the literal
     * @throws NumberFormatException if the given String does not represent a syntactically valid
     *         literal or represents a value out of int range
     */
    public IntLiteral(ExtList children, String valStr) {
        super(children);
        this.value = parseFromString(valStr);
        this.valueStr = Long.toString(value).intern();
    }

    @Override
    public void visit(Visitor v) {
        v.performActionOnIntLiteral(this);
    }

    @Override
    public KeYJavaType getKeYJavaType(Services javaServ) {
        return javaServ.getJavaInfo().getKeYJavaType(PrimitiveType.JAVA_INT);
    }

    @Override
    public long getValue() {
        return value;
    }

    @Override
    public String getValueString() {
        return valueStr;
    }

    /**
     * Parses the String and extracts the actual value of the literal. This method is able to parse
     * literals as described in the Java 8 Language Specification: hexadecimal (beginning with
     * '0x'), decimal, octal (beginning with '0'), and binary (beginning with '0b') literals. In
     * addition, underscores are allowed as separators inside the literal. All values parsed by this
     * method are checked for range correctly, particularly considering the asymmetric range of int.
     * Hexadecimal, octal and binary literals are converted using two's complement.
     *
     * @param sourceStr the String containing the value
     * @return the parsed value as a long
     * @throws NumberFormatException if the given String does not represent a syntactically valid
     *         literal or represents a value out of int range
     * @see <a href="http://docs.oracle.com/javase/specs/jls/se8/html/jls-3.html#jls-3.10.1">
     *      http://docs.oracle.com/javase/specs/jls/se8/html/jls-3.html#jls-3.10.1</a>
     */
    protected int parseFromString(final String sourceStr) throws NumberFormatException {

        String valStr = sourceStr;
        int radix = 10;
        boolean neg = false;

        ///////////////////////////////////////////////////////////////////////////
        /* preprocessing of the input string: */

        // remove minus sign for easier removal of prefix
        if (valStr.startsWith("-")) {
            neg = true;
            valStr = valStr.substring(1);
        }

        // remove underscores
        valStr = valStr.replace("_", "");

        // remove prefix indicating the radix
        if (valStr.startsWith("0x") || valStr.startsWith("0X")) { // hex
            radix = 16;
            valStr = valStr.substring(2); // cut of '0x'
        } else if (valStr.startsWith("0b") || valStr.startsWith("0B")) { // bin
            radix = 2;
            valStr = valStr.substring(2); // cut of '0b'
        } else if (valStr.startsWith("0") && valStr.length() > 1) { // oct
            radix = 8;
            valStr = valStr.substring(1); // cut of leading '0'
        }

        // add minus sign again
        if (neg) {
            valStr = "-" + valStr;
        }

        ///////////////////////////////////////////////////////////////////////////
        /* range check and actual conversion: */

        /*
         * the raw long converted from the input String without considering allowed value range or
         * two's complement
         */
        long val = 0;
        try {
            val = Long.parseLong(valStr, radix);
        } catch (NumberFormatException e) {
            // refer to int here to give a meaningful error message to the user
            throw new NumberFormatException("Not a parsable int: " + valStr);
        }

        // calculate maximum valid range for the literal (depending on sign and radix)
        long maxValue;
        long minValue;
        if (radix == 10) {
            minValue = Integer.MIN_VALUE;
            maxValue = Integer.MAX_VALUE;
        } else {
            maxValue = MAX_UINT;
            minValue = 0;
        }

        // check if literal is in valid range
        if (val > maxValue || val < minValue) {
            // raiseError("Number constant out of bounds: " + literalString, n);
            throw new NumberFormatException("Number constant out of bounds: " + valStr);
        }

        /*
         * perform the actual conversion (two's complement for bin, oct and hex!) of the BigInteger
         * to a String containing the real (checked valid) value of the literal
         */
        return (int) val; // the cast does the two's complement conversion
    }
}

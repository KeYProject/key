/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
// Universitaet Koblenz-Landau, Germany
// Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
// Technical University Darmstadt, Germany
// Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.java.ast.expression.literal;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.Comment;
import de.uka.ilkd.key.java.ast.PositionInfo;
import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.ast.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.visitor.Visitor;
import org.jspecify.annotations.Nullable;

import java.util.List;

/**
 * Int literal.
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

    public IntLiteral(@Nullable PositionInfo pi, @Nullable List<Comment> comments, int value) {
        super(pi, comments);
        this.value = value;
        this.valueStr = "" + value;
    }

    public IntLiteral(@Nullable PositionInfo pi, @Nullable List<Comment> comments,
            String valueStr) {
        super(pi, comments);
        this.valueStr = valueStr;
        value = parseFromString(valueStr);
    }

    /**
     * Creates a new IntLiteral representing the given int.
     *
     * @param value
     *        the int value represented by the literal
     */
    public IntLiteral(int value) {
        this(null, null, value);
    }

    /**
     * Creates a new IntLiteral from the given String. The String is parsed and checked for range.
     * The input may be any String containing a literal as described by the Java 8 Language
     * Specification. This includes hexadecimal, decimal, octal, and binary literals as well as
     * literals containing underscores as separators. In addition, a preceding '-' sign is allowed.
     *
     * @param valStr
     *        the String that contains the literal
     * @throws NumberFormatException
     *         if the given String does not represent a syntactically valid
     *         literal or represents a value out of int range
     * @see <a href="http://docs.oracle.com/javase/specs/jls/se8/html/jls-3.html#jls-3.10.1">
     *      http://docs.oracle.com/javase/specs/jls/se8/html/jls-3.html#jls-3.10.1</a>
     */
    public IntLiteral(String valStr) {
        this(null, null, parseFromString(valStr));
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
     * Parses the String and extracts the actual value of the literal.
     * This method is able to parse literals as described in the Java 8 Language Specification:
     * hexadecimal (beginning with '0x'), decimal, octal (beginning with '0'), and binary
     * (beginning with '0b') literals. In addition, underscores are allowed as separators inside
     * the literal. All values parsed by this method are checked for range correctly, particularly
     * considering the asymmetric range of int.
     * Hexadecimal, octal and binary literals are converted using two's complement.
     *
     * @param sourceStr
     *        the String containing the value
     * @return the parsed value as a long
     * @throws NumberFormatException
     *         if the given String does not represent a syntactically valid
     *         literal or represents a value out of int range
     * @see <a href="http://docs.oracle.com/javase/specs/jls/se8/html/jls-3.html#jls-3.10.1">
     *      http://docs.oracle.com/javase/specs/jls/se8/html/jls-3.html#jls-3.10.1</a>
     */
    protected static int parseFromString(final String sourceStr) throws NumberFormatException {

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
         * the raw long converted from the input String without considering
         * allowed value range or two's complement
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
         * perform the actual conversion (two's complement for bin, oct and hex!) of the
         * BigInteger to a String containing the real (checked valid) value of the literal
         */
        return (int) val; // the cast does the two's complement conversion
    }
}

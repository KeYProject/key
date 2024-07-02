// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.java.expression.literal;

import java.math.BigInteger;

import org.key_project.util.ExtList;

import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.visitor.Visitor;

/**
 *  Long literal.
 *  @author <TT>AutoDoc</TT>
 */

public class LongLiteral extends AbstractIntegerLiteral {

    // constants for range check at String to long conversion
    /**
     * A constant holding the maximum valid value of a signed long: 2<sup>63</sup>-1
     */
    private static final BigInteger MAX_LONG = BigInteger.valueOf(Long.MAX_VALUE);

    /**
     * A constant holding the minimum valid value of a signed long: -2<sup>63</sup>
     */
    private static final BigInteger MIN_LONG = BigInteger.valueOf(Long.MIN_VALUE);

    /**
     * A constant holding the maximum valid value as if a long was interpreted unsigned:
     * : 2<sup>64</sup>-1
     */
    private static final BigInteger MAX_ULONG = new BigInteger("ffffffffffffffff", 16);

    /**
     * Textual representation of the value as a decimal number (always ends with 'L').
     */
    private final String valueStr;

    /**
     * The actual value of the literal.
     */
    private final long value;

    /**
     * Creates a new LongLiteral representing the given long.
     * @param value the long value represented by the literal
     */
    public LongLiteral(long value) {
        this.value = value;
        this.valueStr = (Long.toString(value) + 'L').intern();
    }

    /**
     * Creates a new LongLiteral from the given String. The String is parsed and checked for range.
     * The input may be any String containing a literal as described by the Java 8 Language
     * Specification. This includes hexadecimal, decimal, octal, and binary literals as well as
     * literals containing underscores as separators. In addition, a preceding '-' sign is allowed.
     *
     * @param valStr the String that contains the literal
     * @throws NumberFormatException if the given String does not represent a syntactically valid
     *          literal or represents a value out of long range
     * @see <a href="http://docs.oracle.com/javase/specs/jls/se8/html/jls-3.html#jls-3.10.1">
     *               http://docs.oracle.com/javase/specs/jls/se8/html/jls-3.html#jls-3.10.1</a>
     */
    public LongLiteral(String valStr) {
        this.value = parseFromString(valStr);
        this.valueStr = (Long.toString(value) + 'L').intern();
    }

    /**
     * Constructor for Recoder2KeY transformation.
     *
     * @param children the children of this AST element as KeY classes, may contain: Comments
     * @param valStr the value of the literal
     * @throws NumberFormatException if the given String does not represent a syntactically valid
     *          literal or represents a value out of long range
     */
    public LongLiteral(ExtList children, String valStr) {
        super(children);
        this.value = parseFromString(valStr);
        this.valueStr = (Long.toString(value) + 'L').intern();
    }

    @Override
    public void visit(Visitor v) {
        v.performActionOnLongLiteral(this);
    }

    @Override
    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printLongLiteral(this);
    }

    @Override
    public KeYJavaType getKeYJavaType(Services javaServ) {
        return javaServ.getJavaInfo().getKeYJavaType(PrimitiveType.JAVA_LONG);
    }

    @Override
    public long getValue() {
        return value;
    }

    /**
     *
     * @return the actual value of the literal converted to a decimal String. If the literal
     *         represents a negative value, the first character is a '-' sign.
     *         The returned String always ends with 'L' to indicate a long.
     */
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
     * considering the asymmetric range of long.
     * Hexadecimal, octal and binary literals are converted using two's complement.
     *
     * @param sourceStr the String containing the value
     * @return the parsed value as a long
     * @throws NumberFormatException if the given String does not represent a syntactically valid
     *          literal or represents a value out of long range
     * @see <a href="http://docs.oracle.com/javase/specs/jls/se8/html/jls-3.html#jls-3.10.1">
     *               http://docs.oracle.com/javase/specs/jls/se8/html/jls-3.html#jls-3.10.1</a>
     */
    protected long parseFromString(final String sourceStr) {

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

        // remove long suffix
        if (valStr.endsWith("L") || valStr.endsWith("l")) {
            valStr = valStr.substring(0, valStr.length() - 1);
        }

        if (valStr.startsWith("0x") || valStr.startsWith("0X")) {        // hex
            radix = 16;
            valStr = valStr.substring(2);     // cut of '0x'
        } else if (valStr.startsWith("0b") || valStr.startsWith("0B")) { // bin
            radix = 2;
            valStr = valStr.substring(2);     // cut of '0b'
        } else if (valStr.startsWith("0") && valStr.length() > 1) {      // oct
            radix = 8;
            valStr = valStr.substring(1);     // cut of leading '0'
        }

        // add minus sign again
        if (neg) {
            valStr = "-" + valStr;
        }

        ///////////////////////////////////////////////////////////////////////////
        /* range check and actual conversion: */

        /* the raw BigInteger converted from the input String without considering
         * allowed value range or two's complement
         */
        BigInteger val;
        try {
            val = new BigInteger(valStr, radix);
        } catch (NumberFormatException e) {
            // refer to long here to give a meaningful error message to the user
            throw new NumberFormatException("Not a parsable long: " + valStr);
        }

        // calculate maximum valid magnitude for the literal (depending on sign and radix)
        BigInteger maxValue;
        BigInteger minValue;
        if (radix == 10) {
            maxValue = MAX_LONG;
            minValue = MIN_LONG;
        } else {
            maxValue = MAX_ULONG;
            minValue = BigInteger.ZERO;
        }

        // check if literal is in valid range
        if (val.compareTo(maxValue) > 0 || val.compareTo(minValue) < 0) {
            //raiseError("Number constant out of bounds: " + literalString, n);
            throw new NumberFormatException("Number constant out of bounds: " + sourceStr);
        }

        /* perform the actual conversion (two's complement for bin, oct and hex!) of the
         * BigInteger to a String containing the real (checked valid) value of the literal */
        return val.longValue(); // two's complement conversion
    }
}

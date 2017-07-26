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
 *  Int literal.
 *  @author <TT>AutoDoc</TT>
 */

public class IntLiteral extends AbstractIntegerLiteral {

    // constants for range check at String to int conversion
    /**
     * A constant holding the maximum valid value of a signed int: 2<sup>31</sup>-1
     */
    private static final long MAX_INT = Integer.MAX_VALUE;

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
     * The actual value of the literal. A <code>long</code> is used to be able to represent
     * the absolute value of <code>Integer.MIN_VALUE</code>: 2<sup>31</sup>.
     */
    private final long value;

    /**
     * Creates a new IntLiteral representing the given int.
     * @param value the int value represented by the literal
     */
    public IntLiteral(int value) {
        this.value = value;
        this.valueStr = ("" + value).intern();
    }

    /**
     * Creates a new IntLiteral from the given String. The String is parsed and checked for range.
     * The input may be any String containing a literal as described by the Java 8 Language
     * Specification. This includes hexadecimal, decimal, octal, and binary literals as well as
     * literals containing underscores as separators. In addition, a preceding '-' sign is allowed.
     *
     * @param valStr the String that contains the literal
     * @throws NumberFormatException if the given String does not represent a syntactically valid
     *          literal or represents a value out of int range
     * @see <a href="http://docs.oracle.com/javase/specs/jls/se8/html/jls-3.html#jls-3.10.1">
     *               http://docs.oracle.com/javase/specs/jls/se8/html/jls-3.html#jls-3.10.1</a>
     */
    public IntLiteral(String valStr) {
        this(valStr, false);
    }

    /**
     * Creates a new IntLiteral from the given String. The String is parsed and checked for range.
     * The input may be any String containing a literal as described by the Java 8 Language
     * Specification. This includes hexadecimal, decimal, octal, and binary literals as well as
     * literals containing underscores as separators. In addition, a preceding '-' sign is allowed.
     * If the literal is surrounded by an unary minus, the corresponding flag can be set.
     * This allows to perform a correct range check.
     *
     * @param valStr the String that contains the literal
     * @param surroundedByUnaryMinus used in range check
     * @throws NumberFormatException if the given String does not represent a syntactically valid
     *          literal or represents a value out of int range
     * @see <a href="http://docs.oracle.com/javase/specs/jls/se8/html/jls-3.html#jls-3.10.1">
     *               http://docs.oracle.com/javase/specs/jls/se8/html/jls-3.html#jls-3.10.1</a>
     */
    public IntLiteral(String valStr, boolean surroundedByUnaryMinus) {
        super(surroundedByUnaryMinus);
        this.value = parseFromString(valStr);
        this.valueStr = Long.toString(value).intern();
    }

    /**
     * Constructor for Recoder2KeY transformation.
     *
     * @param children the children of this AST element as KeY classes, may contain: Comments
     * @param valStr the value of the literal
     * @param surroundedByUnaryMinus indicates whether the literal is directly surrounded
     *          by an unary minus (used for correct range check)
     * @throws NumberFormatException if the given String does not represent a syntactically valid
     *          literal or represents a value out of int range
     */
    public IntLiteral(ExtList children, String valStr, boolean surroundedByUnaryMinus) {
        super(children, surroundedByUnaryMinus);
        this.value = parseFromString(valStr);
        this.valueStr = Long.toString(value).intern();
    }

//    @Override
//    public boolean equalsModRenaming(SourceElement o, NameAbstractionTable nat) {
//        if (!(o instanceof IntLiteral)) {
//            return false;
//        }
//        return ((IntLiteral)o).getValueString().equals(getValueString());
//    }

    @Override
    public void visit(Visitor v) {
        v.performActionOnIntLiteral(this);
    }

    @Override
    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printIntLiteral(this);
    }

    @Override
    public KeYJavaType getKeYJavaType(Services javaServ) {
        return javaServ.getJavaInfo().getKeYJavaType(PrimitiveType.JAVA_INT);
    }

    @Override
    public BigInteger getValue() {
        return BigInteger.valueOf(value);
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
     * @param sourceStr the String containing the value
     * @return the parsed value as a long
     * @throws NumberFormatException if the given String does not represent a syntactically valid
     *          literal or represents a value out of int range
     * @see <a href="http://docs.oracle.com/javase/specs/jls/se8/html/jls-3.html#jls-3.10.1">
     *               http://docs.oracle.com/javase/specs/jls/se8/html/jls-3.html#jls-3.10.1</a>
     */
    protected long parseFromString(final String sourceStr) throws NumberFormatException {

        String valStr = sourceStr;
        int radix = 10;

        ///////////////////////////////////////////////////////////////////////////
        /* preprocessing of the input string: */

        // remove underscores
        valStr = valStr.replace("_", "");

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

        ///////////////////////////////////////////////////////////////////////////
        /* preprocessing of the context (literal surrounded by an unary minus?): */

        int isMinus = surroundedByUnaryMinus ? 1 : 0;

        ///////////////////////////////////////////////////////////////////////////
        /* range check and actual conversion: */

        /* the raw long converted from the input String without considering
         * allowed value range or two's complement
         */
        long val = Long.parseLong(valStr, radix);

        // calculate maximum valid magnitude for the literal (depending on sign and radix)
        long maxValue;
        if (radix == 10) {
            maxValue = MAX_INT + isMinus;       // asymmetric range depending on sign!
        } else {
            maxValue = MAX_UINT;
        }

        // check if literal is in valid range
        if (val > maxValue) {
            //raiseError("Number constant out of bounds: " + literalString, n);
            throw new NumberFormatException("Number constant out of bounds: " + valStr);
        }

        /* perform the actual conversion (two's complement for bin, oct and hex!) of the
         * BigInteger to a String containing the real (checked valid) value of the literal
         */
        if (radix == 10) {
            //valueStr = Long.toString(val);
            return val;
        } else {
            //valueStr = Integer.toString((int)val);
            return (int)val;    // the cast does the two's complement conversion
        }
    }
}

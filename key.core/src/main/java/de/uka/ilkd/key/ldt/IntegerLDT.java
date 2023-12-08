/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.ldt;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.java.expression.literal.AbstractIntegerLiteral;
import de.uka.ilkd.key.java.expression.literal.CharLiteral;
import de.uka.ilkd.key.java.expression.literal.IntLiteral;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.JFunction;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.util.Debug;

import org.key_project.logic.Name;
import org.key_project.logic.op.Function;
import org.key_project.util.ExtList;

import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;


/**
 * This class inherits from LDT and implements all method that are necessary to handle integers,
 * shorts and bytes. It caches the symbols declared in integerHeader.key and offers methods to
 * convert java number types to their logic counterpart.
 */
@SuppressWarnings("unused")
public final class IntegerLDT extends LDT {
    private static final Logger LOGGER = LoggerFactory.getLogger(IntegerLDT.class);

    public static final Name NAME = new Name("int");

    // public name constants
    public static final String NEGATIVE_LITERAL_STRING = "neglit";
    public static final Name NUMBERS_NAME = new Name("Z");
    public static final Name CHAR_ID_NAME = new Name("C");

    // the following fields cache the symbols from integerHeader.key.
    // (explanations see there)
    private final JFunction sharp;
    private final JFunction[] numberSymbol = new JFunction[10];
    private final JFunction neglit;
    private final JFunction numbers;
    private final JFunction charID;
    private final JFunction add;
    private final JFunction neg;
    private final JFunction sub;
    private final JFunction mul;
    private final JFunction div;
    private final JFunction mod;
    private final JFunction pow;
    private final JFunction bsum;
    private final JFunction bprod;
    // private final JavaDLFunction min; // handled by the \ifEx operator
    // private final JavaDLFunction max;
    private final JFunction jdiv;
    private final JFunction jmod;
    private final JFunction unaryMinusJint;
    private final JFunction unaryMinusJlong;
    private final JFunction addJint;
    private final JFunction addJlong;
    private final JFunction subJint;
    private final JFunction subJlong;
    private final JFunction mulJint;
    private final JFunction mulJlong;
    private final JFunction modJint;
    private final JFunction modJlong;
    private final JFunction divJint;
    private final JFunction divJlong;

    private final JFunction shiftright;
    private final JFunction shiftleft;
    private final JFunction shiftrightJint;
    private final JFunction shiftrightJlong;
    private final JFunction shiftleftJint;
    private final JFunction shiftleftJlong;
    private final JFunction unsignedshiftrightJint;
    private final JFunction unsignedshiftrightJlong;
    private final JFunction binaryOr;
    private final JFunction binaryXOr;
    private final JFunction binaryAnd;
    private final JFunction orJint;
    private final JFunction orJlong;
    private final JFunction bitwiseNegateJint;
    private final JFunction bitwiseNegateJlong;
    private final JFunction andJint;
    private final JFunction andJlong;
    private final JFunction xorJint;
    private final JFunction xorJlong;
    private final JFunction moduloByte;
    private final JFunction moduloShort;
    private final JFunction moduloInt;
    private final JFunction moduloLong;
    private final JFunction moduloChar;
    private final JFunction checkedUnaryMinusInt;
    private final JFunction checkedUnaryMinusLong;
    private final JFunction checkedBitwiseNegateInt;
    private final JFunction checkedBitwiseNegateLong;
    private final JFunction checkedAddInt;
    private final JFunction checkedAddLong;
    private final JFunction checkedSubInt;
    private final JFunction checkedSubLong;
    private final JFunction checkedMulInt;
    private final JFunction checkedMulLong;
    private final JFunction checkedDivInt;
    private final JFunction checkedDivLong;
    private final JFunction checkedShiftRightInt;
    private final JFunction checkedShiftRightLong;
    private final JFunction checkedShiftLeftInt;
    private final JFunction checkedShiftLeftLong;
    private final JFunction checkedUnsignedShiftRightInt;
    private final JFunction checkedUnsignedShiftRightLong;
    private final JFunction checkedBitwiseOrInt;
    private final JFunction checkedBitwiseOrLong;
    private final JFunction checkedBitwiseAndInt;
    private final JFunction checkedBitwiseAndLong;
    private final JFunction checkedBitwiseXOrInt;
    private final JFunction checkedBitwiseXOrLong;
    private final JFunction javaSubInt;
    private final JFunction javaMulInt;
    private final JFunction javaMod;
    private final JFunction javaDivInt;
    private final JFunction javaDivLong;
    private final JFunction javaCastByte;
    private final JFunction javaCastShort;
    private final JFunction javaCastInt;
    private final JFunction javaCastLong;
    private final JFunction javaCastChar;
    private final JFunction lessThan;
    private final JFunction greaterThan;
    private final JFunction greaterOrEquals;
    private final JFunction lessOrEquals;
    private final JFunction inByte;
    private final JFunction inShort;
    private final JFunction inInt;
    private final JFunction inLong;
    private final JFunction inChar;
    private final JFunction inRangeByte;
    private final JFunction inRangeShort;
    private final JFunction inRangeInt;
    private final JFunction inRangeLong;
    private final JFunction inRangeChar;
    private final JFunction index;
    private final Term one;
    private final Term zero;



    // -------------------------------------------------------------------------
    // constructors
    // -------------------------------------------------------------------------

    public IntegerLDT(Services services) {
        super(NAME, services);

        // initialise caches for function symbols from integerHeader.key
        sharp = addFunction(services, "#");
        for (int i = 0; i < 10; i++) {
            numberSymbol[i] = addFunction(services, String.valueOf(i));
        }
        neglit = addFunction(services, NEGATIVE_LITERAL_STRING);
        numbers = addFunction(services, NUMBERS_NAME.toString());
        assert sharp.sort() == numbers.argSort(0);
        charID = addFunction(services, CHAR_ID_NAME.toString());
        add = addFunction(services, "add");
        neg = addFunction(services, "neg");
        sub = addFunction(services, "sub");
        mul = addFunction(services, "mul");
        div = addFunction(services, "div");
        mod = addFunction(services, "mod");
        bsum = addFunction(services, "bsum");
        bprod = addFunction(services, "bprod");
        jdiv = addFunction(services, "jdiv");
        jmod = addFunction(services, "jmod");
        pow = addFunction(services, "pow");
        unaryMinusJint = addFunction(services, "unaryMinusJint");
        unaryMinusJlong = addFunction(services, "unaryMinusJlong");
        addJint = addFunction(services, "addJint");
        addJlong = addFunction(services, "addJlong");
        subJint = addFunction(services, "subJint");
        subJlong = addFunction(services, "subJlong");
        mulJint = addFunction(services, "mulJint");
        mulJlong = addFunction(services, "mulJlong");
        modJint = addFunction(services, "modJint");
        modJlong = addFunction(services, "modJlong");
        divJint = addFunction(services, "divJint");
        divJlong = addFunction(services, "divJlong");

        shiftright = addFunction(services, "shiftright");
        shiftleft = addFunction(services, "shiftleft");
        shiftrightJint = addFunction(services, "shiftrightJint");
        shiftrightJlong = addFunction(services, "shiftrightJlong");
        shiftleftJint = addFunction(services, "shiftleftJint");
        shiftleftJlong = addFunction(services, "shiftleftJlong");
        unsignedshiftrightJint = addFunction(services, "unsignedshiftrightJint");
        unsignedshiftrightJlong = addFunction(services, "unsignedshiftrightJlong");
        binaryOr = addFunction(services, "binaryOr");
        binaryAnd = addFunction(services, "binaryAnd");
        binaryXOr = addFunction(services, "binaryXOr");
        bitwiseNegateJint = addFunction(services, "bitwiseNegateJint");
        bitwiseNegateJlong = addFunction(services, "bitwiseNegateJlong");
        orJint = addFunction(services, "orJint");
        orJlong = addFunction(services, "orJlong");
        andJint = addFunction(services, "andJint");
        andJlong = addFunction(services, "andJlong");
        xorJint = addFunction(services, "xorJint");
        xorJlong = addFunction(services, "xorJlong");
        moduloByte = addFunction(services, "moduloByte");
        moduloShort = addFunction(services, "moduloShort");
        moduloInt = addFunction(services, "moduloInt");
        moduloLong = addFunction(services, "moduloLong");
        moduloChar = addFunction(services, "moduloChar");

        checkedUnaryMinusInt = addFunction(services, "checkedUnaryMinusInt");
        checkedUnaryMinusLong = addFunction(services, "checkedUnaryMinusLong");
        checkedBitwiseNegateInt = addFunction(services, "checkedBitwiseNegateInt");
        checkedBitwiseNegateLong = addFunction(services, "checkedBitwiseNegateLong");
        checkedAddInt = addFunction(services, "checkedAddInt");
        checkedAddLong = addFunction(services, "checkedAddLong");
        checkedSubInt = addFunction(services, "checkedSubInt");
        checkedSubLong = addFunction(services, "checkedSubLong");
        checkedMulInt = addFunction(services, "checkedMulInt");
        checkedMulLong = addFunction(services, "checkedMulLong");
        checkedDivInt = addFunction(services, "checkedDivInt");
        checkedDivLong = addFunction(services, "checkedDivLong");
        checkedShiftRightInt = addFunction(services, "checkedShiftRightInt");
        checkedShiftRightLong = addFunction(services, "checkedShiftRightLong");
        checkedShiftLeftInt = addFunction(services, "checkedShiftLeftInt");
        checkedShiftLeftLong = addFunction(services, "checkedShiftLeftLong");
        checkedUnsignedShiftRightInt = addFunction(services, "checkedUnsignedShiftRightInt");
        checkedUnsignedShiftRightLong = addFunction(services, "checkedUnsignedShiftRightLong");
        checkedBitwiseOrInt = addFunction(services, "checkedBitwiseOrInt");
        checkedBitwiseOrLong = addFunction(services, "checkedBitwiseOrLong");
        checkedBitwiseAndInt = addFunction(services, "checkedBitwiseAndInt");
        checkedBitwiseAndLong = addFunction(services, "checkedBitwiseAndLong");
        checkedBitwiseXOrInt = addFunction(services, "checkedBitwiseXOrInt");
        checkedBitwiseXOrLong = addFunction(services, "checkedBitwiseXOrLong");

        javaSubInt = addFunction(services, "javaSubInt");
        javaMulInt = addFunction(services, "javaMulInt");
        javaMod = addFunction(services, "javaMod");
        javaDivInt = addFunction(services, "javaDivInt");
        javaDivLong = addFunction(services, "javaDivLong");
        javaCastByte = addFunction(services, "javaCastByte");
        javaCastShort = addFunction(services, "javaCastShort");
        javaCastInt = addFunction(services, "javaCastInt");
        javaCastLong = addFunction(services, "javaCastLong");
        javaCastChar = addFunction(services, "javaCastChar");
        lessThan = addFunction(services, "lt");
        greaterThan = addFunction(services, "gt");
        greaterOrEquals = addFunction(services, "geq");
        lessOrEquals = addFunction(services, "leq");
        inByte = addFunction(services, "inByte");
        inShort = addFunction(services, "inShort");
        inInt = addFunction(services, "inInt");
        inLong = addFunction(services, "inLong");
        inChar = addFunction(services, "inChar");
        inRangeByte = addFunction(services, "inRangeByte");
        inRangeShort = addFunction(services, "inRangeShort");
        inRangeInt = addFunction(services, "inRangeInt");
        inRangeLong = addFunction(services, "inRangeLong");
        inRangeChar = addFunction(services, "inRangeChar");
        index = addFunction(services, "index");

        // cache often used constants
        zero = makeDigit(0, services.getTermBuilder());
        one = makeDigit(1, services.getTermBuilder());
    }


    // -------------------------------------------------------------------------
    // internal methods
    // -------------------------------------------------------------------------

    private boolean isNumberLiteral(Operator f) {
        String n = f.name().toString();
        if (n.length() == 1) {
            char c = n.charAt(0);
            return '0' <= c && c <= '9';
        }
        return false;
    }

    private Term makeDigit(int digit, TermBuilder tb) {
        return tb.func(getNumberSymbol(),
            tb.func(getNumberLiteralFor(digit), tb.func(getNumberTerminator())));
    }


    // -------------------------------------------------------------------------
    // public interface
    // -------------------------------------------------------------------------

    public JFunction getNumberTerminator() {
        return sharp;
    }


    public JFunction getNumberLiteralFor(int number) {
        if (number < 0 || number > 9) {
            throw new IllegalArgumentException(
                "Number literal symbols range from 0 to 9. Requested was:" + number);
        }

        return numberSymbol[number];
    }


    public JFunction getNegativeNumberSign() {
        return neglit;
    }


    public JFunction getNumberSymbol() {
        return numbers;
    }


    public JFunction getCharSymbol() {
        return charID;
    }


    public JFunction getAdd() {
        return add;
    }


    public JFunction getNeg() {
        return neg;
    }


    public JFunction getSub() {
        return sub;
    }


    public JFunction getMul() {
        return mul;
    }


    public JFunction getDiv() {
        return div;
    }


    public JFunction getMod() {
        return mod;
    }


    public JFunction getPow() {
        return pow;
    }


    public JFunction getBsum() {
        return bsum;
    }

    public JFunction getBprod() {
        return bprod;
    }

    public JFunction getLessThan() {
        return lessThan;
    }


    public JFunction getGreaterThan() {
        return greaterThan;
    }


    public JFunction getGreaterOrEquals() {
        return greaterOrEquals;
    }


    public JFunction getLessOrEquals() {
        return lessOrEquals;
    }

    public JFunction getAddJint() {
        return addJint;
    }

    public JFunction getAddJlong() {
        return addJlong;
    }

    public JFunction getSubJint() {
        return subJint;
    }

    public JFunction getSubJlong() {
        return subJlong;
    }

    public JFunction getMulJint() {
        return mulJint;
    }

    public JFunction getMulJlong() {
        return mulJlong;
    }

    public JFunction getModJint() {
        return modJint;
    }

    public JFunction getModJlong() {
        return modJlong;
    }

    public JFunction getDivJint() {
        return divJint;
    }

    public JFunction getDivJlong() {
        return divJlong;
    }

    public JFunction getShiftright() {
        return shiftright;
    }

    public JFunction getShiftleft() {
        return shiftleft;
    }

    public JFunction getShiftrightJint() {
        return shiftrightJint;
    }

    public JFunction getShiftrightJlong() {
        return shiftrightJlong;
    }

    public JFunction getShiftleftJint() {
        return shiftleftJint;
    }

    public JFunction getShiftleftJlong() {
        return shiftleftJlong;
    }

    public JFunction getUnsignedshiftrightJint() {
        return unsignedshiftrightJint;
    }

    public JFunction getUnsignedshiftrightJlong() {
        return unsignedshiftrightJlong;
    }

    public JFunction getBitwiseNegateJint() {
        return bitwiseNegateJint;
    }

    public JFunction getBitwiseNegateJlong() {
        return bitwiseNegateJlong;
    }

    public JFunction getOrJint() {
        return orJint;
    }

    public JFunction getBitwiseOrJlong() {
        return orJlong;
    }

    public JFunction getAndJint() {
        return andJint;
    }

    public JFunction getAndJlong() {
        return andJlong;
    }

    public JFunction getXorJint() {
        return xorJint;
    }

    public JFunction getXorJlong() {
        return xorJlong;
    }

    public JFunction getBitwiseOrJInt() {
        return orJint;
    }

    public JFunction getBitwiseAndJInt() {
        return andJint;
    }

    public JFunction getBitwiseAndJLong() {
        return andJlong;
    }

    public JFunction getUnaryMinusJint() {
        return unaryMinusJint;
    }

    public JFunction getUnaryMinusJlong() {
        return unaryMinusJlong;
    }

    public JFunction getBinaryOr() {
        return binaryOr;
    }

    public JFunction getBinaryXOr() {
        return binaryXOr;
    }

    public JFunction getBinaryAnd() {
        return binaryAnd;
    }

    public JFunction getModuloInt() {
        return moduloInt;
    }

    public JFunction getCheckedUnaryMinusInt() {
        return checkedUnaryMinusInt;
    }

    public JFunction getCheckedUnaryMinusLong() {
        return checkedUnaryMinusLong;
    }

    public JFunction getCheckedBitwiseNegateInt() {
        return checkedBitwiseNegateInt;
    }

    public JFunction getCheckedBitwiseNegateLong() {
        return checkedBitwiseNegateLong;
    }

    public JFunction getCheckedAddInt() {
        return checkedAddInt;
    }

    public JFunction getCheckedAddLong() {
        return checkedAddLong;
    }

    public JFunction getCheckedSubInt() {
        return checkedSubInt;
    }

    public JFunction getCheckedSubLong() {
        return checkedSubLong;
    }

    public JFunction getCheckedMulInt() {
        return checkedMulInt;
    }

    public JFunction getCheckedMulLong() {
        return checkedMulLong;
    }

    public JFunction getCheckedDivInt() {
        return checkedDivInt;
    }

    public JFunction getCheckedDivLong() {
        return checkedDivLong;
    }

    public JFunction getCheckedShiftRightInt() {
        return checkedShiftRightInt;
    }

    public JFunction getCheckedShiftRightLong() {
        return checkedShiftRightLong;
    }

    public JFunction getCheckedShiftLeftInt() {
        return checkedShiftLeftInt;
    }

    public JFunction getCheckedShiftLeftLong() {
        return checkedShiftLeftLong;
    }

    public JFunction getCheckedUnsignedShiftRightInt() {
        return checkedUnsignedShiftRightInt;
    }

    public JFunction getCheckedUnsignedShiftRightLong() {
        return checkedUnsignedShiftRightLong;
    }

    public JFunction getCheckedBitwiseOrInt() {
        return checkedBitwiseOrInt;
    }

    public JFunction getCheckedBitwiseOrLong() {
        return checkedBitwiseOrLong;
    }

    public JFunction getCheckedBitwiseAndInt() {
        return checkedBitwiseAndInt;
    }

    public JFunction getCheckedBitwiseAndLong() {
        return checkedBitwiseAndLong;
    }

    public JFunction getCheckedBitwiseXOrInt() {
        return checkedBitwiseXOrInt;
    }

    public JFunction getCheckedBitwiseXOrLong() {
        return checkedBitwiseXOrLong;
    }

    /**
     * Placeholder for the loop index variable in an enhanced for loop over arrays. Follows the
     * proposal by David Cok to adapt JML to Java5.
     *
     * @return
     */
    public JFunction getIndex() {
        return index;
    }


    public JFunction getInBounds(Type t) {
        if (t == PrimitiveType.JAVA_BYTE) {
            return inByte;
        } else if (t == PrimitiveType.JAVA_CHAR) {
            return inChar;
        } else if (t == PrimitiveType.JAVA_INT) {
            return inInt;
        } else if (t == PrimitiveType.JAVA_LONG) {
            return inLong;
        } else if (t == PrimitiveType.JAVA_SHORT) {
            return inShort;
        } else {
            return null;
        }
    }

    /**
     * in bounds for specification
     *
     * @param t the type
     * @return in range function
     */
    public JFunction getSpecInBounds(Type t) {
        if (t == PrimitiveType.JAVA_BYTE) {
            return inRangeByte;
        } else if (t == PrimitiveType.JAVA_CHAR) {
            return inRangeChar;
        } else if (t == PrimitiveType.JAVA_INT) {
            return inRangeInt;
        } else if (t == PrimitiveType.JAVA_LONG) {
            return inRangeLong;
        } else if (t == PrimitiveType.JAVA_SHORT) {
            return inRangeShort;
        } else {
            return null;
        }
    }

    /**
     * Finds the cast to type `t`. This is intended for creating specification only.
     *
     * @param t the type
     * @return the cast
     */
    public JFunction getSpecCast(Type t) {
        if (t == PrimitiveType.JAVA_BYTE) {
            return moduloByte;
        } else if (t == PrimitiveType.JAVA_CHAR) {
            return moduloChar;
        } else if (t == PrimitiveType.JAVA_INT) {
            return moduloInt;
        } else if (t == PrimitiveType.JAVA_LONG) {
            return moduloLong;
        } else if (t == PrimitiveType.JAVA_SHORT) {
            return moduloShort;
        } else if (t == PrimitiveType.JAVA_BIGINT) {
            return null;
        } else {
            throw new RuntimeException(
                "IntegerLDT: This is not a type supported by integer ltd: " + t);
        }
    }

    /**
     * returns the function symbol for the given operation null if no function is found for the
     * given operator
     *
     * @return the function symbol for the given operation
     */
    @Override
    public JFunction getFunctionFor(de.uka.ilkd.key.java.expression.Operator op, Services serv,
            ExecutionContext ec) {
        // Dead in all examples, removed in commit 1e72a5709053a87cae8d2
        return null;
    }

    @Nullable
    @Override
    public JFunction getFunctionFor(String op, Services services) {
        return switch (op) {
        case "gt" -> getGreaterThan();
        case "geq" -> getGreaterOrEquals();
        case "lt" -> getLessThan();
        case "leq" -> getLessOrEquals();
        case "div" -> getDiv();
        case "mul" -> getMul();
        case "add" -> getAdd();
        case "sub" -> getSub();
        case "mod" -> getMod();
        case "neg" -> getNeg();
        default -> null;
        };
    }

    @Override
    public boolean isResponsible(de.uka.ilkd.key.java.expression.Operator op, Term[] subs,
            Services services, ExecutionContext ec) {
        return false;
    }



    @Override
    public boolean isResponsible(de.uka.ilkd.key.java.expression.Operator op, Term left, Term right,
            Services services, ExecutionContext ec) {
        return false;
    }


    @Override
    public boolean isResponsible(de.uka.ilkd.key.java.expression.Operator op, Term sub,
            TermServices services, ExecutionContext ec) {
        return false;
    }

    @Override
    public Term translateLiteral(Literal lit, Services services) {
        Debug.assertTrue(lit instanceof AbstractIntegerLiteral,
            "Literal '" + lit + "' is not an integer literal.");

        Term result;
        if (lit instanceof CharLiteral) {
            result = services.getTermBuilder().cTerm(((CharLiteral) lit).getValueString());
        } else {
            result = services.getTermBuilder().zTerm(((AbstractIntegerLiteral) lit).getValue());
        }

        return result;
    }

    @Override
    public boolean hasLiteralFunction(JFunction f) {
        return containsFunction(f) && (f.arity() == 0 || isNumberLiteral(f));
    }

    public String toNumberString(Term t) {
        StringBuilder sb = new StringBuilder();
        Operator f = t.op();
        while (isNumberLiteral(f)) {
            sb.insert(0, f.name().toString().charAt(0));
            t = t.sub(0);
            f = t.op();
        }

        if (f != sharp) {
            throw new RuntimeException("IntegerLDT: This is not a numeral literal: " + t);
        }

        return sb.toString();
    }

    @Override
    public Expression translateTerm(Term t, ExtList children, Services services) {
        if (!containsFunction((Function) t.op())) {
            return null;
        }
        JFunction f = (JFunction) t.op();
        if (isNumberLiteral(f) || f == numbers || f == charID) {

            Term it = t;
            if (f == charID || f == numbers) {
                it = it.sub(0);
            }

            return new IntLiteral(toNumberString(it)); // TODO: what if number too large for int?
        }
        throw new RuntimeException("IntegerLDT: Cannot convert term to program: " + t);
    }


    @Override
    public Type getType(Term t) {
        assert false : "IntegerLDT: Cannot get Java type for term: " + t;
        return null;
    }



    /**
     * returns the function symbol used to represent java-like division of the arithmetical integers
     *
     * @return the function symbol used to represent integer division
     */
    public JFunction getJDivision() {
        return jdiv;
    }

    /**
     * returns the function symbol used to represent the modulo operation of the arithmetical
     * integers
     *
     * @return the function symbol used to represent the integer modulo operation
     */
    public JFunction getArithModulo() {
        return mod;
    }

    /**
     * returns the function symbol used to represent the java-like modulo operation of the
     * arithmetical integers
     *
     * @return the function symbol used to represent the integer modulo operation
     */
    public JFunction getJModulo() {
        return jmod;
    }

    /** returns a function mapping an arithmetic integer to its Java long representation */
    public JFunction getModuloLong() {
        return modJlong;
    }

    /** maps an integer back into long range */
    public JFunction getArithModuloLong() {
        return modJlong;
    }

    /** maps an integer back into int range */
    public JFunction getArithModuloInt() {
        return moduloInt;
    }

    /** maps an integer back into long range */
    public JFunction getArithModuloShort() {
        return moduloShort;
    }

    /** maps an integer back into byte range */
    public JFunction getArithModuloByte() {
        return moduloByte;
    }

    /** maps an integer back into char range */
    public JFunction getArithModuloChar() {
        return moduloChar;
    }

    /**
     * returns the function symbol interpreted as the Java addition on int (or promotabel to int)
     * operators, i.e. this addition performs a modulo operation wrt. to the range of type
     * <code>int</code>. This function is independent of the chosen integer semantics.
     *
     * @return mathematical interpreted function realising the Java addition on operands of or
     *         promotable to type <code>int</code>
     */
    public JFunction getArithJavaIntAddition() {
        return addJint;
    }


    /**
     * returns the function symbol representing the bitwise-or for Java int
     */
    public JFunction getBitwiseOrJavaInt() {
        return orJint;
    }

    /**
     * the function representing the Java operator <code>(byte)</code>
     *
     * @return function representing the generic Java operator JavaDLFunction
     */
    public JFunction getJavaCastByte() {
        return javaCastByte;
    }

    /**
     * the function representing the Java operator <code>(char)</code>
     *
     * @return function representing the generic Java operator function
     */
    public JFunction getJavaCastChar() {
        return javaCastChar;
    }


    /**
     * the function representing the Java operator <code>(int)</code>
     *
     * @return function representing the generic Java operator function
     */
    public JFunction getJavaCastInt() {
        return javaCastInt;
    }

    /**
     * the function representing the Java operator <code>(long)</code>
     *
     * @return function representing the generic Java operator function
     */
    public JFunction getJavaCastLong() {
        return javaCastLong;
    }

    /**
     * the function representing the Java operator <code>(short)</code>
     *
     * @return function representing the generic Java operator function
     */
    public JFunction getJavaCastShort() {
        return javaCastShort;
    }

    /**
     * the function representing the Java operator <code>/</code> when one of the operands is an or
     * a subtype of int
     *
     * @return function representing the generic Java operator function
     */
    public JFunction getJavaDivInt() {
        return javaDivInt;
    }

    /**
     * the function representing the Java operator <code>/</code> when one of the operands is exact
     * of type long
     *
     * @return function representing the generic Java operator function
     */
    public JFunction getJavaDivLong() {
        return javaDivLong;
    }


    /**
     * the function representing the Java operator <code>%</code> when one of the operands is an or
     * a subtype of int
     *
     * @return function representing the generic Java operator function
     */
    public JFunction getJavaMod() {
        return javaMod;
    }


    /**
     * the function representing the Java operator <code>*</code> when one of the operands is an or
     * a subtype of int
     *
     * @return function representing the generic Java operator function
     */
    public JFunction getJavaMulInt() {
        return javaMulInt;
    }

    /**
     * the function representing the Java operator <code>-</code> when one of the operands is an or
     * a subtype of int
     *
     * @return function representing the generic Java operator function
     */
    public JFunction getJavaSubInt() {
        return javaSubInt;
    }

    public Term zero() {
        return zero;
    }

    public Term one() {
        return one;
    }
}

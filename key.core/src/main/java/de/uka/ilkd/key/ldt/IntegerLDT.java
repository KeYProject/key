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
import org.key_project.logic.op.Function;
import de.uka.ilkd.key.logic.op.JavaDLFunction;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.util.Debug;

import org.key_project.logic.Name;
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
    private final JavaDLFunction sharp;
    private final JavaDLFunction[] numberSymbol = new JavaDLFunction[10];
    private final JavaDLFunction neglit;
    private final JavaDLFunction numbers;
    private final JavaDLFunction charID;
    private final JavaDLFunction add;
    private final JavaDLFunction neg;
    private final JavaDLFunction sub;
    private final JavaDLFunction mul;
    private final JavaDLFunction div;
    private final JavaDLFunction mod;
    private final JavaDLFunction pow;
    private final JavaDLFunction bsum;
    private final JavaDLFunction bprod;
    // private final JavaDLFunction min; // handled by the \ifEx operator
    // private final JavaDLFunction max;
    private final JavaDLFunction jdiv;
    private final JavaDLFunction jmod;
    private final JavaDLFunction unaryMinusJint;
    private final JavaDLFunction unaryMinusJlong;
    private final JavaDLFunction addJint;
    private final JavaDLFunction addJlong;
    private final JavaDLFunction subJint;
    private final JavaDLFunction subJlong;
    private final JavaDLFunction mulJint;
    private final JavaDLFunction mulJlong;
    private final JavaDLFunction modJint;
    private final JavaDLFunction modJlong;
    private final JavaDLFunction divJint;
    private final JavaDLFunction divJlong;

    private final JavaDLFunction shiftright;
    private final JavaDLFunction shiftleft;
    private final JavaDLFunction shiftrightJint;
    private final JavaDLFunction shiftrightJlong;
    private final JavaDLFunction shiftleftJint;
    private final JavaDLFunction shiftleftJlong;
    private final JavaDLFunction unsignedshiftrightJint;
    private final JavaDLFunction unsignedshiftrightJlong;
    private final JavaDLFunction binaryOr;
    private final JavaDLFunction binaryXOr;
    private final JavaDLFunction binaryAnd;
    private final JavaDLFunction orJint;
    private final JavaDLFunction orJlong;
    private final JavaDLFunction bitwiseNegateJint;
    private final JavaDLFunction bitwiseNegateJlong;
    private final JavaDLFunction andJint;
    private final JavaDLFunction andJlong;
    private final JavaDLFunction xorJint;
    private final JavaDLFunction xorJlong;
    private final JavaDLFunction moduloByte;
    private final JavaDLFunction moduloShort;
    private final JavaDLFunction moduloInt;
    private final JavaDLFunction moduloLong;
    private final JavaDLFunction moduloChar;
    private final JavaDLFunction checkedUnaryMinusInt;
    private final JavaDLFunction checkedUnaryMinusLong;
    private final JavaDLFunction checkedBitwiseNegateInt;
    private final JavaDLFunction checkedBitwiseNegateLong;
    private final JavaDLFunction checkedAddInt;
    private final JavaDLFunction checkedAddLong;
    private final JavaDLFunction checkedSubInt;
    private final JavaDLFunction checkedSubLong;
    private final JavaDLFunction checkedMulInt;
    private final JavaDLFunction checkedMulLong;
    private final JavaDLFunction checkedDivInt;
    private final JavaDLFunction checkedDivLong;
    private final JavaDLFunction checkedShiftRightInt;
    private final JavaDLFunction checkedShiftRightLong;
    private final JavaDLFunction checkedShiftLeftInt;
    private final JavaDLFunction checkedShiftLeftLong;
    private final JavaDLFunction checkedUnsignedShiftRightInt;
    private final JavaDLFunction checkedUnsignedShiftRightLong;
    private final JavaDLFunction checkedBitwiseOrInt;
    private final JavaDLFunction checkedBitwiseOrLong;
    private final JavaDLFunction checkedBitwiseAndInt;
    private final JavaDLFunction checkedBitwiseAndLong;
    private final JavaDLFunction checkedBitwiseXOrInt;
    private final JavaDLFunction checkedBitwiseXOrLong;
    private final JavaDLFunction javaSubInt;
    private final JavaDLFunction javaMulInt;
    private final JavaDLFunction javaMod;
    private final JavaDLFunction javaDivInt;
    private final JavaDLFunction javaDivLong;
    private final JavaDLFunction javaCastByte;
    private final JavaDLFunction javaCastShort;
    private final JavaDLFunction javaCastInt;
    private final JavaDLFunction javaCastLong;
    private final JavaDLFunction javaCastChar;
    private final JavaDLFunction lessThan;
    private final JavaDLFunction greaterThan;
    private final JavaDLFunction greaterOrEquals;
    private final JavaDLFunction lessOrEquals;
    private final JavaDLFunction inByte;
    private final JavaDLFunction inShort;
    private final JavaDLFunction inInt;
    private final JavaDLFunction inLong;
    private final JavaDLFunction inChar;
    private final JavaDLFunction inRangeByte;
    private final JavaDLFunction inRangeShort;
    private final JavaDLFunction inRangeInt;
    private final JavaDLFunction inRangeLong;
    private final JavaDLFunction inRangeChar;
    private final JavaDLFunction index;
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

    public JavaDLFunction getNumberTerminator() {
        return sharp;
    }


    public JavaDLFunction getNumberLiteralFor(int number) {
        if (number < 0 || number > 9) {
            throw new IllegalArgumentException(
                "Number literal symbols range from 0 to 9. Requested was:" + number);
        }

        return numberSymbol[number];
    }


    public JavaDLFunction getNegativeNumberSign() {
        return neglit;
    }


    public JavaDLFunction getNumberSymbol() {
        return numbers;
    }


    public JavaDLFunction getCharSymbol() {
        return charID;
    }


    public JavaDLFunction getAdd() {
        return add;
    }


    public JavaDLFunction getNeg() {
        return neg;
    }


    public JavaDLFunction getSub() {
        return sub;
    }


    public JavaDLFunction getMul() {
        return mul;
    }


    public JavaDLFunction getDiv() {
        return div;
    }


    public JavaDLFunction getMod() {
        return mod;
    }


    public JavaDLFunction getPow() {
        return pow;
    }


    public JavaDLFunction getBsum() {
        return bsum;
    }

    public JavaDLFunction getBprod() {
        return bprod;
    }

    public JavaDLFunction getLessThan() {
        return lessThan;
    }


    public JavaDLFunction getGreaterThan() {
        return greaterThan;
    }


    public JavaDLFunction getGreaterOrEquals() {
        return greaterOrEquals;
    }


    public JavaDLFunction getLessOrEquals() {
        return lessOrEquals;
    }

    public JavaDLFunction getAddJint() {
        return addJint;
    }

    public JavaDLFunction getAddJlong() {
        return addJlong;
    }

    public JavaDLFunction getSubJint() {
        return subJint;
    }

    public JavaDLFunction getSubJlong() {
        return subJlong;
    }

    public JavaDLFunction getMulJint() {
        return mulJint;
    }

    public JavaDLFunction getMulJlong() {
        return mulJlong;
    }

    public JavaDLFunction getModJint() {
        return modJint;
    }

    public JavaDLFunction getModJlong() {
        return modJlong;
    }

    public JavaDLFunction getDivJint() {
        return divJint;
    }

    public JavaDLFunction getDivJlong() {
        return divJlong;
    }

    public JavaDLFunction getShiftright() {
        return shiftright;
    }

    public JavaDLFunction getShiftleft() {
        return shiftleft;
    }

    public JavaDLFunction getShiftrightJint() {
        return shiftrightJint;
    }

    public JavaDLFunction getShiftrightJlong() {
        return shiftrightJlong;
    }

    public JavaDLFunction getShiftleftJint() {
        return shiftleftJint;
    }

    public JavaDLFunction getShiftleftJlong() {
        return shiftleftJlong;
    }

    public JavaDLFunction getUnsignedshiftrightJint() {
        return unsignedshiftrightJint;
    }

    public JavaDLFunction getUnsignedshiftrightJlong() {
        return unsignedshiftrightJlong;
    }

    public JavaDLFunction getBitwiseNegateJint() {
        return bitwiseNegateJint;
    }

    public JavaDLFunction getBitwiseNegateJlong() {
        return bitwiseNegateJlong;
    }

    public JavaDLFunction getOrJint() {
        return orJint;
    }

    public JavaDLFunction getBitwiseOrJlong() {
        return orJlong;
    }

    public JavaDLFunction getAndJint() {
        return andJint;
    }

    public JavaDLFunction getAndJlong() {
        return andJlong;
    }

    public JavaDLFunction getXorJint() {
        return xorJint;
    }

    public JavaDLFunction getXorJlong() {
        return xorJlong;
    }

    public JavaDLFunction getBitwiseOrJInt() {
        return orJint;
    }

    public JavaDLFunction getBitwiseAndJInt() {
        return andJint;
    }

    public JavaDLFunction getBitwiseAndJLong() {
        return andJlong;
    }

    public JavaDLFunction getUnaryMinusJint() {
        return unaryMinusJint;
    }

    public JavaDLFunction getUnaryMinusJlong() {
        return unaryMinusJlong;
    }

    public JavaDLFunction getBinaryOr() {
        return binaryOr;
    }

    public JavaDLFunction getBinaryXOr() {
        return binaryXOr;
    }

    public JavaDLFunction getBinaryAnd() {
        return binaryAnd;
    }

    public JavaDLFunction getModuloInt() {
        return moduloInt;
    }

    public JavaDLFunction getCheckedUnaryMinusInt() {
        return checkedUnaryMinusInt;
    }

    public JavaDLFunction getCheckedUnaryMinusLong() {
        return checkedUnaryMinusLong;
    }

    public JavaDLFunction getCheckedBitwiseNegateInt() {
        return checkedBitwiseNegateInt;
    }

    public JavaDLFunction getCheckedBitwiseNegateLong() {
        return checkedBitwiseNegateLong;
    }

    public JavaDLFunction getCheckedAddInt() {
        return checkedAddInt;
    }

    public JavaDLFunction getCheckedAddLong() {
        return checkedAddLong;
    }

    public JavaDLFunction getCheckedSubInt() {
        return checkedSubInt;
    }

    public JavaDLFunction getCheckedSubLong() {
        return checkedSubLong;
    }

    public JavaDLFunction getCheckedMulInt() {
        return checkedMulInt;
    }

    public JavaDLFunction getCheckedMulLong() {
        return checkedMulLong;
    }

    public JavaDLFunction getCheckedDivInt() {
        return checkedDivInt;
    }

    public JavaDLFunction getCheckedDivLong() {
        return checkedDivLong;
    }

    public JavaDLFunction getCheckedShiftRightInt() {
        return checkedShiftRightInt;
    }

    public JavaDLFunction getCheckedShiftRightLong() {
        return checkedShiftRightLong;
    }

    public JavaDLFunction getCheckedShiftLeftInt() {
        return checkedShiftLeftInt;
    }

    public JavaDLFunction getCheckedShiftLeftLong() {
        return checkedShiftLeftLong;
    }

    public JavaDLFunction getCheckedUnsignedShiftRightInt() {
        return checkedUnsignedShiftRightInt;
    }

    public JavaDLFunction getCheckedUnsignedShiftRightLong() {
        return checkedUnsignedShiftRightLong;
    }

    public JavaDLFunction getCheckedBitwiseOrInt() {
        return checkedBitwiseOrInt;
    }

    public JavaDLFunction getCheckedBitwiseOrLong() {
        return checkedBitwiseOrLong;
    }

    public JavaDLFunction getCheckedBitwiseAndInt() {
        return checkedBitwiseAndInt;
    }

    public JavaDLFunction getCheckedBitwiseAndLong() {
        return checkedBitwiseAndLong;
    }

    public JavaDLFunction getCheckedBitwiseXOrInt() {
        return checkedBitwiseXOrInt;
    }

    public JavaDLFunction getCheckedBitwiseXOrLong() {
        return checkedBitwiseXOrLong;
    }

    /**
     * Placeholder for the loop index variable in an enhanced for loop over arrays. Follows the
     * proposal by David Cok to adapt JML to Java5.
     *
     * @return
     */
    public JavaDLFunction getIndex() {
        return index;
    }


    public JavaDLFunction getInBounds(Type t) {
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
    public JavaDLFunction getSpecInBounds(Type t) {
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
    public JavaDLFunction getSpecCast(Type t) {
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
    public JavaDLFunction getFunctionFor(de.uka.ilkd.key.java.expression.Operator op, Services serv,
                                         ExecutionContext ec) {
        // Dead in all examples, removed in commit 1e72a5709053a87cae8d2
        return null;
    }

    @Nullable
    @Override
    public JavaDLFunction getFunctionFor(String op, Services services) {
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
    public boolean hasLiteralFunction(JavaDLFunction f) {
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
        JavaDLFunction f = (JavaDLFunction) t.op();
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
    public JavaDLFunction getJDivision() {
        return jdiv;
    }

    /**
     * returns the function symbol used to represent the modulo operation of the arithmetical
     * integers
     *
     * @return the function symbol used to represent the integer modulo operation
     */
    public JavaDLFunction getArithModulo() {
        return mod;
    }

    /**
     * returns the function symbol used to represent the java-like modulo operation of the
     * arithmetical integers
     *
     * @return the function symbol used to represent the integer modulo operation
     */
    public JavaDLFunction getJModulo() {
        return jmod;
    }

    /** returns a function mapping an arithmetic integer to its Java long representation */
    public JavaDLFunction getModuloLong() {
        return modJlong;
    }

    /** maps an integer back into long range */
    public JavaDLFunction getArithModuloLong() {
        return modJlong;
    }

    /** maps an integer back into int range */
    public JavaDLFunction getArithModuloInt() {
        return moduloInt;
    }

    /** maps an integer back into long range */
    public JavaDLFunction getArithModuloShort() {
        return moduloShort;
    }

    /** maps an integer back into byte range */
    public JavaDLFunction getArithModuloByte() {
        return moduloByte;
    }

    /** maps an integer back into char range */
    public JavaDLFunction getArithModuloChar() {
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
    public JavaDLFunction getArithJavaIntAddition() {
        return addJint;
    }


    /**
     * returns the function symbol representing the bitwise-or for Java int
     */
    public JavaDLFunction getBitwiseOrJavaInt() {
        return orJint;
    }

    /**
     * the function representing the Java operator <code>(byte)</code>
     *
     * @return function representing the generic Java operator JavaDLFunction
     */
    public JavaDLFunction getJavaCastByte() {
        return javaCastByte;
    }

    /**
     * the function representing the Java operator <code>(char)</code>
     *
     * @return function representing the generic Java operator function
     */
    public JavaDLFunction getJavaCastChar() {
        return javaCastChar;
    }


    /**
     * the function representing the Java operator <code>(int)</code>
     *
     * @return function representing the generic Java operator function
     */
    public JavaDLFunction getJavaCastInt() {
        return javaCastInt;
    }

    /**
     * the function representing the Java operator <code>(long)</code>
     *
     * @return function representing the generic Java operator function
     */
    public JavaDLFunction getJavaCastLong() {
        return javaCastLong;
    }

    /**
     * the function representing the Java operator <code>(short)</code>
     *
     * @return function representing the generic Java operator function
     */
    public JavaDLFunction getJavaCastShort() {
        return javaCastShort;
    }

    /**
     * the function representing the Java operator <code>/</code> when one of the operands is an or
     * a subtype of int
     *
     * @return function representing the generic Java operator function
     */
    public JavaDLFunction getJavaDivInt() {
        return javaDivInt;
    }

    /**
     * the function representing the Java operator <code>/</code> when one of the operands is exact
     * of type long
     *
     * @return function representing the generic Java operator function
     */
    public JavaDLFunction getJavaDivLong() {
        return javaDivLong;
    }


    /**
     * the function representing the Java operator <code>%</code> when one of the operands is an or
     * a subtype of int
     *
     * @return function representing the generic Java operator function
     */
    public JavaDLFunction getJavaMod() {
        return javaMod;
    }


    /**
     * the function representing the Java operator <code>*</code> when one of the operands is an or
     * a subtype of int
     *
     * @return function representing the generic Java operator function
     */
    public JavaDLFunction getJavaMulInt() {
        return javaMulInt;
    }

    /**
     * the function representing the Java operator <code>-</code> when one of the operands is an or
     * a subtype of int
     *
     * @return function representing the generic Java operator function
     */
    public JavaDLFunction getJavaSubInt() {
        return javaSubInt;
    }

    public Term zero() {
        return zero;
    }

    public Term one() {
        return one;
    }
}

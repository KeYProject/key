/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.ldt;

import javax.annotation.Nullable;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.java.expression.literal.AbstractIntegerLiteral;
import de.uka.ilkd.key.java.expression.literal.CharLiteral;
import de.uka.ilkd.key.java.expression.literal.IntLiteral;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.util.Debug;

import org.key_project.util.ExtList;

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
    private final Function sharp;
    private final Function[] numberSymbol = new Function[10];
    private final Function neglit;
    private final Function numbers;
    private final Function charID;
    private final Function add;
    private final Function neg;
    private final Function sub;
    private final Function mul;
    private final Function div;
    private final Function mod;
    private final Function pow;
    private final Function bsum;
    private final Function bprod;
    // private final Function min; // handled by the \ifEx operator
    // private final Function max;
    private final Function jdiv;
    private final Function jmod;
    private final Function unaryMinusJint;
    private final Function unaryMinusJlong;
    private final Function addJint;
    private final Function addJlong;
    private final Function subJint;
    private final Function subJlong;
    private final Function mulJint;
    private final Function mulJlong;
    private final Function modJint;
    private final Function modJlong;
    private final Function divJint;
    private final Function divJlong;

    private final Function shiftright;
    private final Function shiftleft;
    private final Function shiftrightJint;
    private final Function shiftrightJlong;
    private final Function shiftleftJint;
    private final Function shiftleftJlong;
    private final Function unsignedshiftrightJint;
    private final Function unsignedshiftrightJlong;
    private final Function binaryOr;
    private final Function binaryXOr;
    private final Function binaryAnd;
    private final Function orJint;
    private final Function orJlong;
    private final Function bitwiseNegateJint;
    private final Function bitwiseNegateJlong;
    private final Function andJint;
    private final Function andJlong;
    private final Function xorJint;
    private final Function xorJlong;
    private final Function moduloByte;
    private final Function moduloShort;
    private final Function moduloInt;
    private final Function moduloLong;
    private final Function moduloChar;
    private final Function checkedUnaryMinusInt;
    private final Function checkedUnaryMinusLong;
    private final Function checkedBitwiseNegateInt;
    private final Function checkedBitwiseNegateLong;
    private final Function checkedAddInt;
    private final Function checkedAddLong;
    private final Function checkedSubInt;
    private final Function checkedSubLong;
    private final Function checkedMulInt;
    private final Function checkedMulLong;
    private final Function checkedDivInt;
    private final Function checkedDivLong;
    private final Function checkedShiftRightInt;
    private final Function checkedShiftRightLong;
    private final Function checkedShiftLeftInt;
    private final Function checkedShiftLeftLong;
    private final Function checkedUnsignedShiftRightInt;
    private final Function checkedUnsignedShiftRightLong;
    private final Function checkedBitwiseOrInt;
    private final Function checkedBitwiseOrLong;
    private final Function checkedBitwiseAndInt;
    private final Function checkedBitwiseAndLong;
    private final Function checkedBitwiseXOrInt;
    private final Function checkedBitwiseXOrLong;
    private final Function javaSubInt;
    private final Function javaMulInt;
    private final Function javaMod;
    private final Function javaDivInt;
    private final Function javaDivLong;
    private final Function javaCastByte;
    private final Function javaCastShort;
    private final Function javaCastInt;
    private final Function javaCastLong;
    private final Function javaCastChar;
    private final Function lessThan;
    private final Function greaterThan;
    private final Function greaterOrEquals;
    private final Function lessOrEquals;
    private final Function inByte;
    private final Function inShort;
    private final Function inInt;
    private final Function inLong;
    private final Function inChar;
    private final Function inRangeByte;
    private final Function inRangeShort;
    private final Function inRangeInt;
    private final Function inRangeLong;
    private final Function inRangeChar;
    private final Function index;
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

    public Function getNumberTerminator() {
        return sharp;
    }


    public Function getNumberLiteralFor(int number) {
        if (number < 0 || number > 9) {
            throw new IllegalArgumentException(
                "Number literal symbols range from 0 to 9. Requested was:" + number);
        }

        return numberSymbol[number];
    }


    public Function getNegativeNumberSign() {
        return neglit;
    }


    public Function getNumberSymbol() {
        return numbers;
    }


    public Function getCharSymbol() {
        return charID;
    }


    public Function getAdd() {
        return add;
    }


    public Function getNeg() {
        return neg;
    }


    public Function getSub() {
        return sub;
    }


    public Function getMul() {
        return mul;
    }


    public Function getDiv() {
        return div;
    }


    public Function getMod() {
        return mod;
    }


    public Function getPow() {
        return pow;
    }


    public Function getBsum() {
        return bsum;
    }

    public Function getBprod() {
        return bprod;
    }

    public Function getLessThan() {
        return lessThan;
    }


    public Function getGreaterThan() {
        return greaterThan;
    }


    public Function getGreaterOrEquals() {
        return greaterOrEquals;
    }


    public Function getLessOrEquals() {
        return lessOrEquals;
    }

    public Function getAddJint() {
        return addJint;
    }

    public Function getAddJlong() {
        return addJlong;
    }

    public Function getSubJint() {
        return subJint;
    }

    public Function getSubJlong() {
        return subJlong;
    }

    public Function getMulJint() {
        return mulJint;
    }

    public Function getMulJlong() {
        return mulJlong;
    }

    public Function getModJint() {
        return modJint;
    }

    public Function getModJlong() {
        return modJlong;
    }

    public Function getDivJint() {
        return divJint;
    }

    public Function getDivJlong() {
        return divJlong;
    }

    public Function getShiftright() {
        return shiftright;
    }

    public Function getShiftleft() {
        return shiftleft;
    }

    public Function getShiftrightJint() {
        return shiftrightJint;
    }

    public Function getShiftrightJlong() {
        return shiftrightJlong;
    }

    public Function getShiftleftJint() {
        return shiftleftJint;
    }

    public Function getShiftleftJlong() {
        return shiftleftJlong;
    }

    public Function getUnsignedshiftrightJint() {
        return unsignedshiftrightJint;
    }

    public Function getUnsignedshiftrightJlong() {
        return unsignedshiftrightJlong;
    }

    public Function getBitwiseNegateJint() {
        return bitwiseNegateJint;
    }

    public Function getBitwiseNegateJlong() {
        return bitwiseNegateJlong;
    }

    public Function getOrJint() {
        return orJint;
    }

    public Function getBitwiseOrJlong() {
        return orJlong;
    }

    public Function getAndJint() {
        return andJint;
    }

    public Function getAndJlong() {
        return andJlong;
    }

    public Function getXorJint() {
        return xorJint;
    }

    public Function getXorJlong() {
        return xorJlong;
    }

    public Function getBitwiseOrJInt() {
        return orJint;
    }

    public Function getBitwiseAndJInt() {
        return andJint;
    }

    public Function getBitwiseAndJLong() {
        return andJlong;
    }

    public Function getUnaryMinusJint() {
        return unaryMinusJint;
    }

    public Function getUnaryMinusJlong() {
        return unaryMinusJlong;
    }

    public Function getBinaryOr() {
        return binaryOr;
    }

    public Function getBinaryXOr() {
        return binaryXOr;
    }

    public Function getBinaryAnd() {
        return binaryAnd;
    }

    public Function getModuloInt() {
        return moduloInt;
    }

    public Function getCheckedUnaryMinusInt() {
        return checkedUnaryMinusInt;
    }

    public Function getCheckedUnaryMinusLong() {
        return checkedUnaryMinusLong;
    }

    public Function getCheckedBitwiseNegateInt() {
        return checkedBitwiseNegateInt;
    }

    public Function getCheckedBitwiseNegateLong() {
        return checkedBitwiseNegateLong;
    }

    public Function getCheckedAddInt() {
        return checkedAddInt;
    }

    public Function getCheckedAddLong() {
        return checkedAddLong;
    }

    public Function getCheckedSubInt() {
        return checkedSubInt;
    }

    public Function getCheckedSubLong() {
        return checkedSubLong;
    }

    public Function getCheckedMulInt() {
        return checkedMulInt;
    }

    public Function getCheckedMulLong() {
        return checkedMulLong;
    }

    public Function getCheckedDivInt() {
        return checkedDivInt;
    }

    public Function getCheckedDivLong() {
        return checkedDivLong;
    }

    public Function getCheckedShiftRightInt() {
        return checkedShiftRightInt;
    }

    public Function getCheckedShiftRightLong() {
        return checkedShiftRightLong;
    }

    public Function getCheckedShiftLeftInt() {
        return checkedShiftLeftInt;
    }

    public Function getCheckedShiftLeftLong() {
        return checkedShiftLeftLong;
    }

    public Function getCheckedUnsignedShiftRightInt() {
        return checkedUnsignedShiftRightInt;
    }

    public Function getCheckedUnsignedShiftRightLong() {
        return checkedUnsignedShiftRightLong;
    }

    public Function getCheckedBitwiseOrInt() {
        return checkedBitwiseOrInt;
    }

    public Function getCheckedBitwiseOrLong() {
        return checkedBitwiseOrLong;
    }

    public Function getCheckedBitwiseAndInt() {
        return checkedBitwiseAndInt;
    }

    public Function getCheckedBitwiseAndLong() {
        return checkedBitwiseAndLong;
    }

    public Function getCheckedBitwiseXOrInt() {
        return checkedBitwiseXOrInt;
    }

    public Function getCheckedBitwiseXOrLong() {
        return checkedBitwiseXOrLong;
    }

    /**
     * Placeholder for the loop index variable in an enhanced for loop over arrays. Follows the
     * proposal by David Cok to adapt JML to Java5.
     *
     * @return
     */
    public Function getIndex() {
        return index;
    }


    public Function getInBounds(Type t) {
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
    public Function getSpecInBounds(Type t) {
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
    public Function getSpecCast(Type t) {
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
    public Function getFunctionFor(de.uka.ilkd.key.java.expression.Operator op, Services serv,
            ExecutionContext ec) {
        // Dead in all examples, removed in commit 1e72a5709053a87cae8d2
        return null;
    }

    @Nullable
    @Override
    public Function getFunctionFor(String op, Services services) {
        switch (op) {
        case "gt":
            return getGreaterThan();
        case "geq":
            return getGreaterOrEquals();
        case "lt":
            return getLessThan();
        case "leq":
            return getLessOrEquals();
        case "div":
            return getDiv();
        case "mul":
            return getMul();
        case "add":
            return getAdd();
        case "sub":
            return getSub();
        case "mod":
            return getMod();
        case "neg":
            return getNeg();
        }
        return null;
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
    public boolean hasLiteralFunction(Function f) {
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
        Function f = (Function) t.op();
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
    public Function getJDivision() {
        return jdiv;
    }

    /**
     * returns the function symbol used to represent the modulo operation of the arithmetical
     * integers
     *
     * @return the function symbol used to represent the integer modulo operation
     */
    public Function getArithModulo() {
        return mod;
    }

    /**
     * returns the function symbol used to represent the java-like modulo operation of the
     * arithmetical integers
     *
     * @return the function symbol used to represent the integer modulo operation
     */
    public Function getJModulo() {
        return jmod;
    }

    /** returns a function mapping an arithmetic integer to its Java long representation */
    public Function getModuloLong() {
        return modJlong;
    }

    /** maps an integer back into long range */
    public Function getArithModuloLong() {
        return modJlong;
    }

    /** maps an integer back into int range */
    public Function getArithModuloInt() {
        return moduloInt;
    }

    /** maps an integer back into long range */
    public Function getArithModuloShort() {
        return moduloShort;
    }

    /** maps an integer back into byte range */
    public Function getArithModuloByte() {
        return moduloByte;
    }

    /** maps an integer back into char range */
    public Function getArithModuloChar() {
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
    public Function getArithJavaIntAddition() {
        return addJint;
    }


    /**
     * returns the function symbol representing the bitwise-or for Java int
     */
    public Function getBitwiseOrJavaInt() {
        return orJint;
    }

    /**
     * the function representing the Java operator <code>(byte)</code>
     *
     * @return function representing the generic Java operator function
     */
    public Function getJavaCastByte() {
        return javaCastByte;
    }

    /**
     * the function representing the Java operator <code>(char)</code>
     *
     * @return function representing the generic Java operator function
     */
    public Function getJavaCastChar() {
        return javaCastChar;
    }


    /**
     * the function representing the Java operator <code>(int)</code>
     *
     * @return function representing the generic Java operator function
     */
    public Function getJavaCastInt() {
        return javaCastInt;
    }

    /**
     * the function representing the Java operator <code>(long)</code>
     *
     * @return function representing the generic Java operator function
     */
    public Function getJavaCastLong() {
        return javaCastLong;
    }

    /**
     * the function representing the Java operator <code>(short)</code>
     *
     * @return function representing the generic Java operator function
     */
    public Function getJavaCastShort() {
        return javaCastShort;
    }

    /**
     * the function representing the Java operator <code>/</code> when one of the operands is an or
     * a subtype of int
     *
     * @return function representing the generic Java operator function
     */
    public Function getJavaDivInt() {
        return javaDivInt;
    }

    /**
     * the function representing the Java operator <code>/</code> when one of the operands is exact
     * of type long
     *
     * @return function representing the generic Java operator function
     */
    public Function getJavaDivLong() {
        return javaDivLong;
    }


    /**
     * the function representing the Java operator <code>%</code> when one of the operands is an or
     * a subtype of int
     *
     * @return function representing the generic Java operator function
     */
    public Function getJavaMod() {
        return javaMod;
    }


    /**
     * the function representing the Java operator <code>*</code> when one of the operands is an or
     * a subtype of int
     *
     * @return function representing the generic Java operator function
     */
    public Function getJavaMulInt() {
        return javaMulInt;
    }

    /**
     * the function representing the Java operator <code>-</code> when one of the operands is an or
     * a subtype of int
     *
     * @return function representing the generic Java operator function
     */
    public Function getJavaSubInt() {
        return javaSubInt;
    }

    public Term zero() {
        return zero;
    }

    public Term one() {
        return one;
    }
}

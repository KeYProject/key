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

package de.uka.ilkd.key.speclang.translation;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.TypeConverter;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.ldt.*;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.ldt.IntegerLDT;
import javax.annotation.Nonnull;
import java.util.HashMap;
import java.util.List;
import java.util.Map;


/**
 * Helper class for sl-parsers dealing with Java's type promotion for integers.
 */
public class JMLArithmeticHelper {

    Services services;
    private final TermBuilder tb;

    private final SLExceptionFactory excManager;
    private final TypeConverter tc;
    private final IntegerLDT integerLDT;
    private final FloatLDT floatLDT;
    private final DoubleLDT doubleLDT;
    private final RealLDT realLDT;

    /* Names in the LDT lookup tables are not the operators, but
     * string versions, so we have to keep a map. */
    // FIXME when Java 11 is allowed
    private static final Map<String, String> COMPARISON_MAP = /*Map.*/HACKHACKof(
            ">=", "geq", "<=", "leq", ">", "gt",
            "<", "lt"
            );

    // FIXME when Java 11 is allowed
    private static Map<String, String> HACKHACKof(String... strings) {
        assert strings.length % 2 == 0;
        HashMap result = new HashMap();
        for (int i = 0; i < strings.length; i+=2) {
            result.put(strings[i], strings[i+1]);
        }
        return result;
    }

    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------

    public JMLArithmeticHelper(Services services,
                               SLExceptionFactory excManager) {
        assert services != null;
        assert excManager != null;

        this.services = services;
        this.excManager = excManager;
        this.tc = services.getTypeConverter();
        this.tb = services.getTermBuilder();
        this.integerLDT = services.getTypeConverter().getIntegerLDT();
        this.floatLDT = services.getTypeConverter().getFloatLDT();
        this.doubleLDT = services.getTypeConverter().getDoubleLDT();
        this.realLDT = null; // bound to fail. FIXME with the code below.
        // TODO ADD THIS WHEN AVAILABLE this.realLDT = services.getTypeConverter().getRealLDT();
    }


    //-------------------------------------------------------------------------
    //internal methods
    //-------------------------------------------------------------------------

    private void raiseError(String message) throws SLTranslationException {
        throw excManager.createException(message);
    }

    private void raiseError(String message, Exception e) throws SLTranslationException {
        throw excManager.createException(message, e);
    }


    private KeYJavaType getPromotedType(SLExpression a, SLExpression b) {
        KeYJavaType result = tc.getPromotedType(a.getType(), b.getType());
        assert result != null;
        return result;
    }

    private KeYJavaType getPromotedType(SLExpression a) {
        KeYJavaType result = tc.getPromotedType(a.getType());
        assert result != null;
        return result;
    }

    private Term promote(Term term, KeYJavaType resultType) {
        Sort targetSort = resultType.getSort();
        if (term.sort() != targetSort) {
            return tb.cast(targetSort, term);
        } else {
            return term;
        }
    }

    private boolean isBigint(KeYJavaType resultType) {
        return resultType.getJavaType() == PrimitiveType.JAVA_BIGINT;
    }

    private boolean isLong(KeYJavaType resultType) {
        return resultType.getJavaType() == PrimitiveType.JAVA_LONG;
    }

    private boolean isFloat(KeYJavaType resultType) {
        return resultType.getJavaType() == PrimitiveType.JAVA_FLOAT;
    }

    private boolean isDouble(KeYJavaType resultType) {
        return resultType.getJavaType() == PrimitiveType.JAVA_DOUBLE;
    }

    private boolean isReal(KeYJavaType resultType) {
        return resultType.getJavaType() == PrimitiveType.JAVA_REAL;
    }



    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------

    public boolean isIntegerTerm(@Nonnull SLExpression a) {
        assert a.isTerm();
        return a.getTerm().sort() == integerLDT.targetSort();
    }

    public SLExpression buildPromotedOrExpression(@Nonnull SLExpression a, @Nonnull SLExpression b)
            throws SLTranslationException {
        assert a != null;
        assert b != null;
        try {
            KeYJavaType resultType = getPromotedType(a, b);
            Function or = null;
            if (isLong(resultType))
                or = integerLDT.getJavaBitwiseOrLong();
            else if (isBigint(resultType))
                raiseError("Bitwise operations are not allowed for \\bigint.");
            else
                or = integerLDT.getJavaBitwiseOrInt();
            return new SLExpression(tb.func(or, a.getTerm(), b.getTerm()),
                    resultType);
        } catch (RuntimeException e) {
            raiseError("Error in or-expression " + a + " | " + b + ".",e);
            return null; //unreachable
        }
    }


    public SLExpression buildPromotedAndExpression(SLExpression a,
                                                   SLExpression b)
            throws SLTranslationException {
        assert a != null;
        assert b != null;
        try {
            KeYJavaType resultType = getPromotedType(a, b);
            Function and = null;
            if (isLong(resultType))
                and = integerLDT.getJavaBitwiseAndLong();
            else if (isBigint(resultType))
                raiseError("Bitwise operations are not allowed for \\bigint.");
            else
                and = integerLDT.getJavaBitwiseAndInt();
            return new SLExpression(tb.func(and, a.getTerm(), b.getTerm()),
                    resultType);
        } catch (RuntimeException e) {
            raiseError("Error in and-expression " + a + " & " + b + ".",e);
            return null; //unreachable
        }
    }


    public SLExpression buildPromotedXorExpression(SLExpression a,
                                                   SLExpression b)
            throws SLTranslationException {
        assert a != null;
        assert b != null;
        try {
            KeYJavaType resultType = getPromotedType(a, b);
            Function xor = null;
            if (isLong(resultType))
                xor = integerLDT.getJavaBitwiseXOrLong();
            else if (isBigint(resultType))
                raiseError("Bitwise operations are not allowed for \\bigint.");
            else
                xor = integerLDT.getJavaBitwiseXOrInt();
            return new SLExpression(tb.func(xor, a.getTerm(), b.getTerm()),
                    resultType);
        } catch (RuntimeException e) {
            raiseError("Error in xor-expression " + a + " ^ " + b + ".",e);
            return null; //unreachable
        }
    }


    public SLExpression buildPromotedNegExpression(SLExpression a)
            throws SLTranslationException {
        assert a != null;
        try {
            if (isBigint(a.getType()))
                raiseError("Bitwise operations are not allowed for \\bigint.");
            Function neg = integerLDT.getJavaBitwiseNegation();
            return new SLExpression(tb.func(neg, a.getTerm()),
                    a.getType());
        } catch (RuntimeException e) {
            raiseError("Error in neg-expression " + a + ".",e);
            return null; //unreachable
        }
    }

    public SLExpression buildComparisonExpression(SLExpression a, SLExpression b, String opStr)
            throws SLTranslationException {
        assert a != null;
        assert b != null;
        try {
            KeYJavaType resultType = getPromotedType(a, b);
            Function fun;
            LDT ldt;
            if (isReal(resultType))
                ldt = realLDT;
            else if (isFloat(resultType))
                ldt = floatLDT;
            else if (isDouble(resultType))
                ldt = doubleLDT;
            else // int, long, or bigint does not matter
                ldt = integerLDT;
            fun = ldt.getFunctionFor(opStr, services);
            if (fun == null) {
                raiseError("Operator " + opStr + " not defined for " + ldt.name());
            }
            return new SLExpression(tb.func(fun,
                    promote(a.getTerm(), resultType),
                    promote(b.getTerm(), resultType)));
        } catch (RuntimeException e) {
            raiseError("Error in comparison expression " + a + " " + opStr + " " + b, e);
            return null; //unreachable
        }
    }

    public SLExpression buildAddExpression(SLExpression a, SLExpression b)
            throws SLTranslationException {
        assert a != null;
        assert b != null;
        try {
            KeYJavaType resultType = getPromotedType(a, b);
            Function add;
            if (isLong(resultType))
                add = integerLDT.getJavaAddLong();
            else if (isBigint(resultType))
                add = integerLDT.getAdd();
            else if (isReal(resultType))
                add = null; // FIXME realLDT.getAdd();
            else if (isFloat(resultType))
                add = floatLDT.getJavaAdd();
            else if (isDouble(resultType))
                add = doubleLDT.getJavaAdd();
            else
                add = integerLDT.getJavaAddInt();
            return new SLExpression(tb.func(add,
                    promote(a.getTerm(), resultType),
                    promote(b.getTerm(), resultType)),
                    resultType);
        } catch (RuntimeException e) {
            raiseError("Error in additive expression " + a + " + " + b + ":", e);
            return null; //unreachable
        }
    }

    public SLExpression buildSubExpression(SLExpression a, SLExpression b)
            throws SLTranslationException {
        assert a != null;
        assert b != null;
        try {
            KeYJavaType resultType = getPromotedType(a, b);
            Function sub;
            if (isLong(resultType))
                sub = integerLDT.getJavaSubLong();
            else if (isBigint(resultType))
                sub = integerLDT.getSub();
            else if (isReal(resultType))
                sub = null; // FIXME realLDT.getSub();
            else if (isFloat(resultType))
            sub = floatLDT.getJavaSub();
            else if (isDouble(resultType))
            sub = doubleLDT.getJavaSub();
            else
                sub = integerLDT.getJavaSubInt();
            return new SLExpression(tb.func(sub,
                    promote(a.getTerm(), resultType),
                    promote(b.getTerm(), resultType)),
                    resultType);
        } catch (RuntimeException e) {
            raiseError("Error in subtract expression " + a + " - " + b + ".",e);
            return null; //unreachable            
        }
    }

    public SLExpression buildMultExpression(SLExpression a, SLExpression b)
            throws SLTranslationException {
        assert a != null;
        assert b != null;
        try {
            KeYJavaType resultType = getPromotedType(a, b);
            Function mul;
            if (isLong(resultType))
                mul = integerLDT.getJavaMulLong();
            else if (isBigint(resultType))
                mul = integerLDT.getMul();
            else if (isReal(resultType))
                mul = null; // FIXME realLDT.getmul();
            else if (isFloat(resultType))
                mul = floatLDT.getJavaMul();
            else if (isDouble(resultType))
                mul = doubleLDT.getJavaMul();
            else
                mul = integerLDT.getJavaMulInt();
            return new SLExpression(tb.func(mul,
                    promote(a.getTerm(), resultType),
                    promote(b.getTerm(), resultType)),
                    resultType);
        } catch (RuntimeException e) {
            raiseError("Error in multiplicative expression " + a + " * "
                    + b + ".",e);
            return null; //unreachable            
        }
    }

    public SLExpression buildDivExpression(SLExpression a, SLExpression b)
            throws SLTranslationException {
        try {
            KeYJavaType resultType = getPromotedType(a, b);
            Function div;
            if (isLong(resultType))
                div = integerLDT.getJavaDivLong();
            else if (isBigint(resultType))
                div = integerLDT.getJDivision();
            else if (isReal(resultType))
                div = null; // FIXME realLDT.getdiv();
            else if (isFloat(resultType))
                div = floatLDT.getJavaDiv();
            else if (isDouble(resultType))
                div = doubleLDT.getJavaDiv();
            else
                div = integerLDT.getJavaDivInt();
            return new SLExpression(tb.func(div,
                    promote(a.getTerm(), resultType),
                    promote(b.getTerm(), resultType)),
                    resultType);
        } catch (RuntimeException e) {
            raiseError("Error in division expression " + a + " / " + b + ".",e);
            return null; //unreachable            
        }
    }


    public SLExpression buildModExpression(SLExpression a, SLExpression b)
            throws SLTranslationException {
        assert a != null;
        assert b != null;
        try {
            KeYJavaType resultType = getPromotedType(a, b);
            if (isBigint(resultType))
                return new SLExpression(tb.func(integerLDT.getJModulo(), a.getTerm(), b.getTerm()), resultType);
            else
                return new SLExpression(tb.func(integerLDT.getJavaMod(), a.getTerm(), b.getTerm()),
                        a.getType());
        } catch (RuntimeException e) {
            raiseError("Error in modulo expression " + a + " % " + b + ".",e);
            return null; //unreachable            
        }
    }


    public SLExpression buildRightShiftExpression(SLExpression a, SLExpression b)
            throws SLTranslationException {
        assert a != null;
        assert b != null;
        try {
            KeYJavaType resultType = getPromotedType(a, b);
            Function shift = null;
            if (isLong(resultType)) {
                shift = integerLDT.getJavaShiftRightLong();
            } else if (isBigint(resultType)){
                raiseError("Shift operation not allowed for \\bigint.");
            } else {
                shift = integerLDT.getJavaShiftRightInt();
            }
            return new SLExpression(tb.func(shift, a.getTerm(), b.getTerm()),
                    resultType);
        } catch (RuntimeException e) {
            raiseError("Error in shift-right expression " + a + " >> "
                    + b + ".",e);
            return null; //unreachable            
        }
    }

    public SLExpression buildLeftShiftExpression(SLExpression a, SLExpression b)
            throws SLTranslationException {
        assert a != null;
        assert b != null;
        try {
            KeYJavaType resultType = getPromotedType(a, b);
            Function shift = null;
            if (isLong(resultType))
                shift = integerLDT.getJavaShiftLeftLong();
            else if (isBigint(resultType))
                raiseError("Shift operation not allowed for \\bigint.");
            else
                shift = integerLDT.getJavaShiftLeftInt();
            return new SLExpression(tb.func(shift, a.getTerm(), b.getTerm()),
                    resultType);
        } catch (RuntimeException e) {
            raiseError("Error in shift-left expression " + a + " << "
                    + b + ".",e);
            return null; //unreachable            
        }
    }


    public SLExpression buildUnsignedRightShiftExpression(SLExpression a,
                                                          SLExpression b)
            throws SLTranslationException {
        assert a != null;
        assert b != null;
        try {
            KeYJavaType resultType = getPromotedType(a, b);
            Function shift = null;
            if (isLong(resultType))
                shift = integerLDT.getJavaUnsignedShiftRightLong();
            else if (isBigint(resultType))
                raiseError("Shift operation not allowed for \\bigint.");
            else
                shift = integerLDT.getJavaUnsignedShiftRightInt();
            return new SLExpression(tb.func(shift, a.getTerm(), b.getTerm()),
                    resultType);
        } catch (RuntimeException e) {
            raiseError("Error in unsigned shift-right expression " + a + " >>> "
                    + b + ".",e);
            return null; //unreachable            
        }
    }


    public SLExpression buildUnaryMinusExpression(SLExpression a)
            throws SLTranslationException {
        assert a != null;
        try {
            KeYJavaType resultType = getPromotedType(a);
            Function minus;
            if (isLong(resultType))
                minus = integerLDT.getJavaUnaryMinusLong();
            else if (isBigint(resultType))
                minus = integerLDT.getNegativeNumberSign();
            else if (isReal(resultType))
                minus = null; // FIXME realLDT.getminus();
            else if (isFloat(resultType))
                minus = floatLDT.getJavaUnaryMinus();
            else if (isDouble(resultType))
                minus = doubleLDT.getJavaUnaryMinus();
            else
                minus = integerLDT.getJavaUnaryMinusInt();
            return new SLExpression(tb.func(minus, a.getTerm()),
                    resultType);
        } catch (RuntimeException e) {
            raiseError("Error in unary minus expression -" + a + ".",e);
            return null; //unreachable            
        }
    }


    public SLExpression buildPromotedUnaryPlusExpression(SLExpression a)
            throws SLTranslationException {
        return a;
    }


    public SLExpression buildCastExpression(KeYJavaType resultType,
                                            SLExpression a)
            throws SLTranslationException {
        assert a != null;
        try {
            Function cast = integerLDT.getJavaCast(resultType.getJavaType());
            if (cast != null)
                return new SLExpression(tb.func(cast, a.getTerm()), resultType);
            else { // there is no cast to \bigint
                if (! isBigint(resultType))
                    raiseError("Cannot cast expression "+a+" to "+resultType+".");
                return new SLExpression(a.getTerm(), resultType);
            }
        } catch (RuntimeException e) {
            raiseError("Error in cast expression -" + a + ".",e);
            return null; //unreachable            
        }
    }

    public static boolean hasFloatingPoint(SLExpression a, SLExpression b, Services services) {
        Sort floatSort = services.getTypeConverter().getFloatLDT().targetSort();
        Sort doubleSort = services.getTypeConverter().getDoubleLDT().targetSort();
        Sort aSort = a.getTerm().sort();
        Sort bSort = b.getTerm().sort();
        return aSort == floatSort || aSort == doubleSort || bSort == floatSort || bSort == doubleSort;
    }

    public SLExpression buildEqualityExpression(SLExpression a, SLExpression b) throws SLTranslationException {
            assert a != null;
            assert b != null;
            try {
                KeYJavaType promotedType = getPromotedType(a, b);
                Function eq;
                if (isFloat(promotedType)) {
                    eq = floatLDT.getEquals();
                } else eq = doubleLDT.getEquals();
                Term termA = promote(a.getTerm(), promotedType);
                Term termB = promote(b.getTerm(), promotedType);
                Term result = tb.func(eq, termA, termB);
                return new SLExpression(result);
            } catch (RuntimeException e) {
                throw new SLTranslationException("Error in equality expression " + a + " == " + b + ".", e);
            }
    }

}
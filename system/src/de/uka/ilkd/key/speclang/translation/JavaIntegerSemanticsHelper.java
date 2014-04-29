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
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Function;


/**
 * Helper class for sl-parsers dealing with Java's type promotion for integers.
 */
public class JavaIntegerSemanticsHelper {

    private final TermBuilder tb; 

    private final SLTranslationExceptionManager excManager;
    private final TypeConverter tc;
    private final IntegerLDT integerLDT;


    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------

    public JavaIntegerSemanticsHelper(Services services,
			    SLTranslationExceptionManager excManager) {
	assert services != null;
	assert excManager != null;

	this.excManager = excManager;
	this.tc = services.getTypeConverter();
	this.tb = services.getTermBuilder();
	this.integerLDT = services.getTypeConverter().getIntegerLDT();
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

    private boolean isBigint(KeYJavaType resultType) {
        return resultType.getJavaType() == PrimitiveType.JAVA_BIGINT;
    }



    private boolean isLong(KeYJavaType resultType) {
        return resultType.getJavaType() == PrimitiveType.JAVA_LONG;
    }

    
    
    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------

    public boolean isIntegerTerm(SLExpression a) throws SLTranslationException {
	assert a.isTerm();
	return a.getTerm().sort() == integerLDT.targetSort();
    }


    public SLExpression buildPromotedOrExpression(SLExpression a, 
	    				          SLExpression b)
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
            else
                add = integerLDT.getJavaAddInt();
            return new SLExpression(tb.func(add, a.getTerm(), b.getTerm()),
                    resultType);
        } catch (RuntimeException e) {
            raiseError("Error in additive expression " + a + " + " + b + ":",e);
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
            if (isLong(resultType)) {
                sub = integerLDT.getJavaSubLong();
            } else if (isBigint(resultType))
                sub = integerLDT.getSub();
            else
                sub = integerLDT.getJavaSubInt();
            return new SLExpression(tb.func(sub, a.getTerm(), b.getTerm()),
                    resultType);
        } catch (RuntimeException e) {
            raiseError("Error in subtract expression " + a + " - " + b + ".",e);
            return null; //unreachable            
        }
    }


    public SLExpression buildMulExpression(SLExpression a, SLExpression b)
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
            else
                mul = integerLDT.getJavaMulInt();
            return new SLExpression(tb.func(mul, a.getTerm(), b.getTerm()),
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
                div = integerLDT.getDiv();
            else
                div = integerLDT.getJavaDivInt();

            return new SLExpression(tb.func(div, a.getTerm(), b.getTerm()),
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
                return new SLExpression(tb.func(integerLDT.getMod(), a.getTerm(), b.getTerm()), resultType);
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
}
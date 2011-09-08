// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
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

    private static final TermBuilder TB = TermBuilder.DF;

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
	this.integerLDT = services.getTypeConverter().getIntegerLDT();
    }
    
    
    
    //-------------------------------------------------------------------------
    //internal methods
    //-------------------------------------------------------------------------

    private void raiseError(String message) throws SLTranslationException {
	throw excManager.createException(message);
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
	    Function or = resultType.getJavaType() == PrimitiveType.JAVA_LONG
	                  ? integerLDT.getJavaBitwiseOrLong()
	                  : integerLDT.getJavaBitwiseOrInt();
	    return new SLExpression(TB.func(or, a.getTerm(), b.getTerm()), 
		                    resultType);
	} catch (RuntimeException e) {
            raiseError("Error in or-expression " + a + " | " + b + ".");
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
	    Function and = resultType.getJavaType() == PrimitiveType.JAVA_LONG
	                  ? integerLDT.getJavaBitwiseAndLong()
	                  : integerLDT.getJavaBitwiseAndInt();
	    return new SLExpression(TB.func(and, a.getTerm(), b.getTerm()),
		                    resultType);
	} catch (RuntimeException e) {
            raiseError("Error in and-expression " + a + " & " + b + ".");
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
	    Function xor = resultType.getJavaType() == PrimitiveType.JAVA_LONG
	                   ? integerLDT.getJavaBitwiseXOrLong()
	                   : integerLDT.getJavaBitwiseXOrInt();
	    return new SLExpression(TB.func(xor, a.getTerm(), b.getTerm()),
		                    resultType);
	} catch (RuntimeException e) {
            raiseError("Error in xor-expression " + a + " ^ " + b + ".");
            return null; //unreachable
        }
    }


    public SLExpression buildPromotedNegExpression(SLExpression a)
	    throws SLTranslationException {
        assert a != null;
	try {
	    Function neg = integerLDT.getJavaBitwiseNegation();
	    return new SLExpression(TB.func(neg, a.getTerm()),
		                    a.getType());
	} catch (RuntimeException e) {
            raiseError("Error in neg-expression " + a + ".");
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
            if (resultType.getJavaType() == PrimitiveType.JAVA_LONG)
                add = integerLDT.getJavaAddLong();
            else if (resultType.getJavaType() == PrimitiveType.JAVA_BIGINT)
                add = integerLDT.getAdd();
            else
                add = integerLDT.getJavaAddInt();
            return new SLExpression(TB.func(add, a.getTerm(), b.getTerm()),
                    resultType);
        } catch (RuntimeException e) {
            raiseError("Error in additive expression " + a + " + " + b + ":" 
                    + e.getMessage());
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
            if (resultType.getJavaType() == PrimitiveType.JAVA_LONG) {
                sub = integerLDT.getJavaSubLong();
            } else if (resultType.getJavaType() == PrimitiveType.JAVA_BIGINT)
                sub = integerLDT.getSub();
            else
                sub = integerLDT.getJavaSubInt();
            return new SLExpression(TB.func(sub, a.getTerm(), b.getTerm()),
                    resultType);
        } catch (RuntimeException e) {
            raiseError("Error in subtract expression " + a + " - " + b + ".");
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
            if (resultType.getJavaType() == PrimitiveType.JAVA_LONG)
                mul = integerLDT.getJavaMulLong();
            else if (resultType.getJavaType() == PrimitiveType.JAVA_BIGINT)
                mul = integerLDT.getMul();
            else
                mul = integerLDT.getJavaMulInt();
            return new SLExpression(TB.func(mul, a.getTerm(), b.getTerm()),
                    resultType);
        } catch (RuntimeException e) {
            raiseError("Error in multiplicative expression " + a + " * "
                    + b + ".");
            return null; //unreachable            
        }
    }


    public SLExpression buildDivExpression(SLExpression a, SLExpression b)
    throws SLTranslationException {
        try {
            KeYJavaType resultType = getPromotedType(a, b);
            Function div;
            if (resultType.getJavaType() == PrimitiveType.JAVA_LONG)
                div = integerLDT.getJavaDivLong();
            else if (resultType.getJavaType() == PrimitiveType.JAVA_BIGINT)
                div = integerLDT.getDiv();
            else
                div = integerLDT.getJavaDivInt();

            return new SLExpression(TB.func(div, a.getTerm(), b.getTerm()),
                    resultType);
        } catch (RuntimeException e) {
            raiseError("Error in division expression " + a + " / " + b + ".");
            return null; //unreachable            
        }
    }


    public SLExpression buildModExpression(SLExpression a, SLExpression b)
    throws SLTranslationException {
        assert a != null;
        assert b != null;
        try {
            KeYJavaType resultType = getPromotedType(a, b);
            if (resultType.getJavaType() == PrimitiveType.JAVA_BIGINT)
                return new SLExpression(TB.func(integerLDT.getMod(), a.getTerm(), b.getTerm()), resultType);
            else
                return new SLExpression(TB.func(integerLDT.getJavaMod(), a.getTerm(), b.getTerm()),
                        a.getType());
        } catch (RuntimeException e) {
            raiseError("Error in modulo expression " + a + " % " + b + ".");
            return null; //unreachable            
        }        
    }


    public SLExpression buildRightShiftExpression(SLExpression a, SLExpression b)
    throws SLTranslationException {
        assert a != null;
        assert b != null;
        try {
            KeYJavaType resultType = getPromotedType(a, b);
            Function shift = resultType.getJavaType() == PrimitiveType.JAVA_LONG
            ? integerLDT.getJavaShiftRightLong()
                    : integerLDT.getJavaShiftRightInt();
            return new SLExpression(TB.func(shift, a.getTerm(), b.getTerm()),
                    resultType);
        } catch (RuntimeException e) {
            raiseError("Error in shift-right expression " + a + " >> " 
                    + b + ".");
            return null; //unreachable            
        }
    }


    public SLExpression buildLeftShiftExpression(SLExpression a, SLExpression b)
    throws SLTranslationException {
        assert a != null;
        assert b != null;
        try {
            KeYJavaType resultType = getPromotedType(a, b);
            Function shift = resultType.getJavaType() == PrimitiveType.JAVA_LONG
            ? integerLDT.getJavaShiftLeftLong()
                    : integerLDT.getJavaShiftLeftInt();
            return new SLExpression(TB.func(shift, a.getTerm(), b.getTerm()),
                    resultType);
        } catch (RuntimeException e) {
            raiseError("Error in shift-left expression " + a + " << " 
                    + b + ".");
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
            Function shift = resultType.getJavaType() == PrimitiveType.JAVA_LONG
            ? integerLDT.getJavaUnsignedShiftRightLong()
                    : integerLDT.getJavaUnsignedShiftRightInt();
            return new SLExpression(TB.func(shift, a.getTerm(), b.getTerm()),
                    resultType);
        } catch (RuntimeException e) {
            raiseError("Error in unsigned shift-right expression " + a + " >>> "
                    + b + ".");
            return null; //unreachable            
        }
    }


    public SLExpression buildUnaryMinusExpression(SLExpression a) 
    throws SLTranslationException {
        assert a != null;
        try {
            KeYJavaType resultType = getPromotedType(a);
            Function minus;
            if (resultType.getJavaType() == PrimitiveType.JAVA_LONG)
                minus = integerLDT.getJavaUnaryMinusLong();
            else if (resultType.getJavaType() == PrimitiveType.JAVA_BIGINT)
                minus = integerLDT.getNegativeNumberSign();
            else
                minus = integerLDT.getJavaUnaryMinusInt();
            return new SLExpression(TB.func(minus, a.getTerm()),
                    resultType);
        } catch (RuntimeException e) {
            raiseError("Error in unary minus expression -" + a + ".");
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
            return new SLExpression(TB.func(cast, a.getTerm()), resultType);
	    else { // there is no cast to \bigint
	        assert resultType.getJavaType() == PrimitiveType.JAVA_BIGINT;
	        return new SLExpression(a.getTerm(), resultType);
	    }
        } catch (RuntimeException e) {
            raiseError("Error in cast expression -" + a + ".");
            return null; //unreachable            
        }
    }    
}

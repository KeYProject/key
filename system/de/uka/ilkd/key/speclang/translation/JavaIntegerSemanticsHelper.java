// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
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
import de.uka.ilkd.key.logic.Term;
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
    
    
    private KeYJavaType getPromotedType(Term a, Term b) {
        KeYJavaType result = tc.getPromotedType(tc.getKeYJavaType(a), 
                                                tc.getKeYJavaType(b));
        assert result != null;
        return result;
    }
    
    
    private KeYJavaType getPromotedType(Term a) {
        KeYJavaType result = tc.getPromotedType(tc.getKeYJavaType(a));
        assert result != null;
        return result;
    }
    
    
    
    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------

    public boolean isIntegerTerm(Term a) throws SLTranslationException {
	return a.sort() == integerLDT.targetSort();
    }


    public Term buildPromotedOrExpression(Term a, Term b)
	    throws SLTranslationException {
        assert a != null;
        assert b != null;
	try {
	    KeYJavaType resultType = getPromotedType(a, b);
	    Function or = resultType.getJavaType() == PrimitiveType.JAVA_LONG
	                  ? integerLDT.getJavaBitwiseOrLong()
	                  : integerLDT.getJavaBitwiseOrInt();
	    return TB.func(or, a, b);
	} catch (RuntimeException e) {
            raiseError("Error in or-expression " + a + " | " + b + ".");
            return null; //unreachable
        }
    }


    public Term buildPromotedAndExpression(Term a, Term b)
	    throws SLTranslationException {
        assert a != null;
        assert b != null;
	try {
	    KeYJavaType resultType = getPromotedType(a, b);
	    Function and = resultType.getJavaType() == PrimitiveType.JAVA_LONG
	                  ? integerLDT.getJavaBitwiseAndLong()
	                  : integerLDT.getJavaBitwiseAndInt();
	    return TB.func(and, a, b);
	} catch (RuntimeException e) {
            raiseError("Error in and-expression " + a + " & " + b + ".");
            return null; //unreachable
        }
    }


    public Term buildPromotedXorExpression(Term a, Term b)
	    throws SLTranslationException {
        assert a != null;
        assert b != null;
	try {
	    KeYJavaType resultType = getPromotedType(a, b);
	    Function xor = resultType.getJavaType() == PrimitiveType.JAVA_LONG
	                   ? integerLDT.getJavaBitwiseXOrLong()
	                   : integerLDT.getJavaBitwiseXOrInt();
	    return TB.func(xor, a, b);
	} catch (RuntimeException e) {
            raiseError("Error in xor-expression " + a + " ^ " + b + ".");
            return null; //unreachable
        }
    }


    public Term buildPromotedNegExpression(Term a)
	    throws SLTranslationException {
        assert a != null;
	try {
	    Function neg = integerLDT.getJavaBitwiseNegation();
	    return TB.func(neg, a);
	} catch (RuntimeException e) {
            raiseError("Error in neg-expression " + a + ".");
            return null; //unreachable
        }
    }


    public Term buildAddExpression(Term a, Term b)
            throws SLTranslationException {
        assert a != null;
        assert b != null;
        try {
            KeYJavaType resultType = getPromotedType(a, b);
            Function add = resultType.getJavaType() == PrimitiveType.JAVA_LONG
                           ? integerLDT.getJavaAddLong()
                           : integerLDT.getJavaAddInt();
            return TB.func(add, a, b);
        } catch (RuntimeException e) {
            raiseError("Error in additive expression " + a + " + " + b + ".");
            return null; //unreachable
        }
    }


    public Term buildSubExpression(Term a, Term b)
            throws SLTranslationException {
        assert a != null;
        assert b != null;
        try {
            KeYJavaType resultType = getPromotedType(a, b);
            Function sub = resultType.getJavaType() == PrimitiveType.JAVA_LONG
                           ? integerLDT.getJavaSubLong()
                           : integerLDT.getJavaSubInt();
            return TB.func(sub, a, b);
        } catch (RuntimeException e) {
            raiseError("Error in subtract expression " + a + " - " + b + ".");
            return null; //unreachable            
        }
    }


    public Term buildMulExpression(Term a, Term b)
            throws SLTranslationException {
        assert a != null;
        assert b != null;
        try {
            KeYJavaType resultType = getPromotedType(a, b);
	    Function mul = resultType.getJavaType() == PrimitiveType.JAVA_LONG
	                   ? integerLDT.getJavaMulLong()
	                   : integerLDT.getJavaMulInt();
            return TB.func(mul, a, b);
        } catch (RuntimeException e) {
            raiseError("Error in multiplicative expression " + a + " * "
                       + b + ".");
            return null; //unreachable            
        }
    }


    public Term buildDivExpression(Term a, Term b)
            throws SLTranslationException {
        try {
            KeYJavaType resultType = getPromotedType(a, b);
	    Function div = resultType.getJavaType() == PrimitiveType.JAVA_LONG
	                   ? integerLDT.getJavaDivLong()
	                   : integerLDT.getJavaDivInt();
 
            return TB.func(div, a, b);         
        } catch (RuntimeException e) {
            raiseError("Error in division expression " + a + " / " + b + ".");
            return null; //unreachable            
        }
    }


    public Term buildModExpression(Term a, Term b)
            throws SLTranslationException {
        assert a != null;
        assert b != null;
        try {
	    Function mod = integerLDT.getJavaMod();
            return TB.func(mod, a, b);
        } catch (RuntimeException e) {
            raiseError("Error in modulo expression " + a + " % " + b + ".");
            return null; //unreachable            
        }        
    }


    public Term buildRightShiftExpression(Term a, Term b)
            throws SLTranslationException {
        assert a != null;
        assert b != null;
        try {
            KeYJavaType resultType = getPromotedType(a, b);
	    Function shift = resultType.getJavaType() == PrimitiveType.JAVA_LONG
	                     ? integerLDT.getJavaShiftRightLong()
	                     : integerLDT.getJavaShiftRightInt();
            return TB.func(shift, a, b);
        } catch (RuntimeException e) {
            raiseError("Error in shift-right expression " + a + " >> " 
                       + b + ".");
            return null; //unreachable            
        }
    }


    public Term buildLeftShiftExpression(Term a, Term b)
            throws SLTranslationException {
        assert a != null;
        assert b != null;
        try {
            KeYJavaType resultType = getPromotedType(a, b);
	    Function shift = resultType.getJavaType() == PrimitiveType.JAVA_LONG
	                     ? integerLDT.getJavaShiftLeftLong()
	                     : integerLDT.getJavaShiftLeftInt();
            return TB.func(shift, a, b);
        } catch (RuntimeException e) {
            raiseError("Error in shift-left expression " + a + " << " 
                       + b + ".");
            return null; //unreachable            
        }
    }


    public Term buildUnsignedRightShiftExpression(Term a, Term b)
            throws SLTranslationException {
        assert a != null;
        assert b != null;
        try {
            KeYJavaType resultType = getPromotedType(a, b);
	    Function shift = resultType.getJavaType() == PrimitiveType.JAVA_LONG
	                     ? integerLDT.getJavaUnsignedShiftRightLong()
	                     : integerLDT.getJavaUnsignedShiftRightInt();
            return TB.func(shift, a, b);
        } catch (RuntimeException e) {
            raiseError("Error in unsigned shift-right expression " + a + " >>> "
                       + b + ".");
            return null; //unreachable            
        }
    }


    public Term buildUnaryMinusExpression(Term a) 
            throws SLTranslationException {
        assert a != null;
        try {
            KeYJavaType resultType = getPromotedType(a);
	    Function minus = resultType.getJavaType() == PrimitiveType.JAVA_LONG
	                     ? integerLDT.getJavaUnaryMinusLong()
	                     : integerLDT.getJavaUnaryMinusInt();
            return TB.func(minus, a);
        } catch (RuntimeException e) {
            raiseError("Error in unary minus expression -" + a + ".");
            return null; //unreachable            
        }
    }


    public Term buildPromotedUnaryPlusExpression(Term a)
            throws SLTranslationException {
	return a;
    }
}

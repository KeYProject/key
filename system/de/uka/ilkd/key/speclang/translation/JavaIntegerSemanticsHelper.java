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
import de.uka.ilkd.key.ldt.AbstractIntegerLDT;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.sort.AbstractSort;


/**
 * Helper class for sl-parsers dealing with Java's type promotion for integers.
 */
public class JavaIntegerSemanticsHelper {

    private static final TermBuilder TB = TermBuilder.DF;

    private final SLTranslationExceptionManager excManager;
    private final TypeConverter tc;


    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------

    public JavaIntegerSemanticsHelper(Services services,
			    SLTranslationExceptionManager excManager) {
	assert services != null;
	assert excManager != null;

	this.excManager = excManager;
	this.tc = services.getTypeConverter();
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
    
    
    private AbstractIntegerLDT getResponsibleIntegerLDT(KeYJavaType kjt) {
        AbstractIntegerLDT result 
            = (AbstractIntegerLDT) tc.getModelFor(kjt.getSort());
        assert result != null;
        return result;
    }
    
    
    
    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------

    public boolean isIntegerTerm(Term a) throws SLTranslationException {
        assert a != null;
        try {
            return a.sort().extendsTrans(tc.getIntegerLDT().targetSort());
        } catch(RuntimeException e) {
            raiseError("Cannot check whether " + a + " is an integer term.");
            return false; //unreachable
        }
    }

   
    public Term castToLDTSort(Term intTerm, AbstractIntegerLDT ldt) 
            throws SLTranslationException {
        assert intTerm != null;
        try {
            return TB.tf().createCastTerm((AbstractSort) ldt.targetSort(), 
                                           intTerm);
        } catch(RuntimeException e) {
            raiseError("Error casting " + intTerm + " to an ldt sort.");
            return null; //unreachable
        }
    }


    public Term buildPromotedOrExpression(Term a, Term b)
	    throws SLTranslationException {
        assert a != null;
        assert b != null;
	try {
	    KeYJavaType resultType = getPromotedType(a, b);
	    AbstractIntegerLDT ldt = getResponsibleIntegerLDT(resultType);
	    return castToLDTSort(TB.func(ldt.getBitwiseOr(), a, b), ldt);
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
	    AbstractIntegerLDT ldt = getResponsibleIntegerLDT(resultType);
	    return castToLDTSort(TB.func(ldt.getBitwiseAnd(), a, b), ldt);
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
	    AbstractIntegerLDT ldt = getResponsibleIntegerLDT(resultType);
	    return castToLDTSort(TB.func(ldt.getBitwiseXor(), a, b), ldt);
	} catch (RuntimeException e) {
            raiseError("Error in xor-expression " + a + " ^ " + b + ".");
            return null; //unreachable
        }
    }


    public Term buildPromotedNegExpression(Term a)
	    throws SLTranslationException {
        assert a != null;
	try {
	    KeYJavaType resultType = getPromotedType(a);
	    AbstractIntegerLDT ldt = getResponsibleIntegerLDT(resultType);
	    return castToLDTSort(TB.func(ldt.getBitwiseNegation(), a), ldt);
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
            AbstractIntegerLDT ldt = getResponsibleIntegerLDT(resultType);
            return castToLDTSort(TB.func(ldt.getAdd(), a, b), ldt);
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
            AbstractIntegerLDT ldt = getResponsibleIntegerLDT(resultType); 
            return castToLDTSort(TB.func(ldt.getSub(), a, b), ldt);
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
            AbstractIntegerLDT ldt = getResponsibleIntegerLDT(resultType); 
            return castToLDTSort(TB.func(ldt.getMul(), a, b), ldt);
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
            AbstractIntegerLDT ldt = getResponsibleIntegerLDT(resultType); 
            return castToLDTSort(TB.func(ldt.getDiv(), a, b), ldt);         
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
            KeYJavaType resultType = getPromotedType(a, b);
            AbstractIntegerLDT ldt = getResponsibleIntegerLDT(resultType);
            return castToLDTSort(TB.func(ldt.getMod(), a, b), ldt);
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
            AbstractIntegerLDT ldt = getResponsibleIntegerLDT(resultType);
            return castToLDTSort(TB.func(ldt.getShiftRight(), a, b), ldt);
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
            AbstractIntegerLDT ldt = getResponsibleIntegerLDT(resultType);
            return castToLDTSort(TB.func(ldt.getShiftLeft(), a, b), ldt);
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
            AbstractIntegerLDT ldt = getResponsibleIntegerLDT(resultType);
            return castToLDTSort(TB.func(ldt.getUnsignedShiftRight(), a, b), 
                                 ldt);
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
            AbstractIntegerLDT ldt = getResponsibleIntegerLDT(resultType);
            return castToLDTSort(TB.func(ldt.getNeg(), a), ldt);
        } catch (RuntimeException e) {
            raiseError("Error in unary minus expression -" + a + ".");
            return null; //unreachable            
        }
    }


    public Term buildPromotedUnaryPlusExpression(Term a)
            throws SLTranslationException {
        assert a != null;
        try {
            KeYJavaType resultType = getPromotedType(a);
            AbstractIntegerLDT ldt = getResponsibleIntegerLDT(resultType);
            return castToLDTSort(a, ldt);
        } catch (RuntimeException e) {
            raiseError("Error in unary plus expression +" + a + ".");
            return null; //unreachable                        
        }
    }
}

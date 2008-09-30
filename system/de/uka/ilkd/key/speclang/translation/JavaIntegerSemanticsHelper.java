// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
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
import de.uka.ilkd.key.java.expression.literal.BooleanLiteral;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermCreationException;
import de.uka.ilkd.key.logic.ldt.AbstractIntegerLDT;
import de.uka.ilkd.key.logic.sort.AbstractSort;
import de.uka.ilkd.key.logic.sort.Sort;

public class JavaIntegerSemanticsHelper {

    private static final TermBuilder tb = TermBuilder.DF;

    private final SLTranslationExceptionManager excManager;

    private final TypeConverter tc;
    private final Term trueLitTerm;
    private final Sort boolSort;



    public JavaIntegerSemanticsHelper(Services services,
			SLTranslationExceptionManager excManager) {
	assert services != null;

	this.excManager = excManager;
	this.tc = services.getTypeConverter();
	trueLitTerm = services.getTypeConverter().convertToLogicElement(
		BooleanLiteral.TRUE);
	boolSort = services.getJavaInfo().getKeYJavaType(
		PrimitiveType.JAVA_BOOLEAN).getSort();
    }


    private void raiseError(String message) throws SLTranslationException {
	throw excManager.createException(message);
    }


    /*
     * If <code>a</code> is a boolean literal, the method returns the
     * literal as a formula
     */
    private Term convertToFormula(Term a) {

	if (a.sort() == boolSort) {
	    return tb.equals(a, trueLitTerm);
	}        
	return a;
    }


    public Term castToLDTSort(Term intTerm, AbstractIntegerLDT ldt) {
	return tb.tf().createCastTerm((AbstractSort) ldt.targetSort(), intTerm);
    }


    public Term buildOrExpression(Term a, Term b) throws SLTranslationException {

	try {
	    return tb.or(convertToFormula(b), convertToFormula(a));
	} catch (TermCreationException e) {
	    raiseError("Error in or-expression\n" + a.toString() + " || "
		    + b.toString() + ".");
	}

	return null;
    }


    public Term buildAndExpression(Term a, Term b)
	    throws SLTranslationException {

	try {
	    return tb.and(convertToFormula(b), convertToFormula(a));
	} catch (TermCreationException e) {
	    raiseError("Error in and-expression\n" + a.toString() + " && "
		    + b.toString() + ".");
	}

	return null;
    }


    public Term buildPromotedOrExpression(Term a, Term b)
	    throws SLTranslationException {
	KeYJavaType resultType = null;

	if (a.sort() == Sort.FORMULA) {
	    return buildOrExpression(a, b);
	}

	try {
	    resultType = tc.getPromotedType(tc.getKeYJavaType(a), tc
		    .getKeYJavaType(b));
	} catch (RuntimeException e) {
	    raiseError("Error in or expression " + a.toString() + " | "
		    + b.toString() + ".");
	}

	assert resultType != null;

	AbstractIntegerLDT ldt 
	    = (AbstractIntegerLDT) tc.getModelFor(resultType.getSort());
	return castToLDTSort(tb.func(ldt.getBitwiseOr(), a, b), ldt);
    }


    public Term buildPromotedAndExpression(Term a, Term b)
	    throws SLTranslationException {
	KeYJavaType resultType = null;

	if (a.sort() == Sort.FORMULA) {
	    return buildAndExpression(a, b);
	}

	try {
	    resultType = tc.getPromotedType(tc.getKeYJavaType(a), tc
		    .getKeYJavaType(b));
	} catch (RuntimeException e) {
	    raiseError("Error in and expression " + a.toString() + " & "
		    + b.toString() + ".");
	}

	assert resultType != null;

	AbstractIntegerLDT ldt 
	    = (AbstractIntegerLDT) tc.getModelFor(resultType.getSort());
	return castToLDTSort(tb.func(ldt.getBitwiseAnd(), a, b), ldt);
    }


    public Term buildPromotedXorExpression(Term a, Term b)
	    throws SLTranslationException {
	KeYJavaType resultType = null;

	try {
	    resultType = tc.getPromotedType(tc.getKeYJavaType(a), tc
		    .getKeYJavaType(b));
	} catch (RuntimeException e) {
	    raiseError("Error in xor expression " + a.toString() + " ^ "
		    + b.toString() + ".");
	}

	assert resultType != null;

	AbstractIntegerLDT ldt 
	    = (AbstractIntegerLDT) tc.getModelFor(resultType.getSort());
	return castToLDTSort(tb.func(ldt.getBitwiseXor(), a, b), ldt);
    }


    public Term buildPromotedNegExpression(Term a)
	    throws SLTranslationException {
	KeYJavaType resultType = null;

	try {
	    resultType = tc.getPromotedType(tc.getKeYJavaType(a));
	} catch (RuntimeException e) {
	    raiseError("Error in neg expression " + a.toString() + ".");
	}

	assert resultType != null;

	AbstractIntegerLDT ldt 
	    = (AbstractIntegerLDT) tc.getModelFor(resultType.getSort());
	return castToLDTSort(tb.func(ldt.getBitwiseNegation(), a), ldt);
    }


    public Term buildAddExpression(Term a, Term b)
	    throws SLTranslationException {
	KeYJavaType resultType = null;

	try {
	    resultType = tc.getPromotedType(tc.getKeYJavaType(a), tc
		    .getKeYJavaType(b));
	} catch (RuntimeException e) {
            raiseError("Error in additive expression " + a.toString() + " + "
		    + b.toString() + ":\n"+e);
	}

	assert resultType != null;

	AbstractIntegerLDT ldt 
	    = (AbstractIntegerLDT) tc.getModelFor(resultType.getSort());
	return castToLDTSort(tb.func(ldt.getAdd(), a, b), ldt);
    }


    public Term buildSubExpression(Term a, Term b)
	    throws SLTranslationException {
	KeYJavaType resultType = null;

	try {
	    resultType = tc.getPromotedType(tc.getKeYJavaType(a), tc
		    .getKeYJavaType(b));
	} catch (RuntimeException e) {
	    raiseError("Error in additive expression " + a.toString() + " - "
		    + b.toString() + ".");
	}

	assert resultType != null;
	
        AbstractIntegerLDT ldt 
            = (AbstractIntegerLDT) tc.getModelFor(resultType.getSort());
	return castToLDTSort(tb.func(ldt.getSub(), a, b), ldt);
    }


    public Term buildMulExpression(Term a, Term b)
	    throws SLTranslationException {
	KeYJavaType resultType = null;

	try {
	    resultType = tc.getPromotedType(tc.getKeYJavaType(a), tc
		    .getKeYJavaType(b));
	} catch (RuntimeException e) {
	    raiseError("Error in multiplicative expression " + a.toString() + " * "
		    + b.toString() + ".");
	}

	assert resultType != null;

        AbstractIntegerLDT ldt 
            = (AbstractIntegerLDT) tc.getModelFor(resultType.getSort());
	return castToLDTSort(tb.func(((AbstractIntegerLDT) tc
		.getModelFor(resultType.getSort())).getMul(), a, b), ldt);
    }


    public Term buildDivExpression(Term a, Term b)
	    throws SLTranslationException {
	KeYJavaType resultType = null;

	try {
	    resultType = tc.getPromotedType(tc.getKeYJavaType(a), tc
		    .getKeYJavaType(b));
	} catch (RuntimeException e) {
	    raiseError("Error in division expression " + a.toString() + " / "
		    + b.toString() + ".");
	}

	assert resultType != null;

	AbstractIntegerLDT ldt 
	    = (AbstractIntegerLDT) tc.getModelFor(resultType.getSort());
	return castToLDTSort(tb.func(ldt.getDiv(), a, b), ldt);
    }


    public Term buildModExpression(Term a, Term b)
	    throws SLTranslationException {
	KeYJavaType resultType = null;

	try {
	    resultType = tc.getPromotedType(tc.getKeYJavaType(a), tc
		    .getKeYJavaType(b));
	} catch (RuntimeException e) {
	    raiseError("Error in modulo expression " + a.toString() + " % "
		    + b.toString() + ".");
	}

	assert resultType != null;

	AbstractIntegerLDT ldt 
	    = (AbstractIntegerLDT) tc.getModelFor(resultType.getSort());
	return castToLDTSort(tb.func(ldt.getMod(), a, b), ldt);
    }


    public Term buildRightShiftExpression(Term a, Term b)
	    throws SLTranslationException {
	KeYJavaType resultType = null;

	try {
	    resultType = tc.getPromotedType(tc.getKeYJavaType(a), tc
		    .getKeYJavaType(b));
	} catch (RuntimeException e) {
	    raiseError("Error in shift-right expression " + a.toString()
		    + " >> " + b.toString() + ".");
	}

	assert resultType != null;
	
        AbstractIntegerLDT ldt 
            = (AbstractIntegerLDT) tc.getModelFor(resultType.getSort());
	return castToLDTSort(tb.func(ldt.getShiftRight(), a, b), ldt);
    }


    public Term buildLeftShiftExpression(Term a, Term b)
	    throws SLTranslationException {
	KeYJavaType resultType = null;

	try {
	    resultType = tc.getPromotedType(tc.getKeYJavaType(a), tc
		    .getKeYJavaType(b));
	} catch (RuntimeException e) {
	    raiseError("Error in shift-left expression " + a.toString()
		    + " << " + b.toString() + ".");
	}

	assert resultType != null;

	AbstractIntegerLDT ldt 
	    = (AbstractIntegerLDT) tc.getModelFor(resultType.getSort());
	return castToLDTSort(tb.func(ldt.getShiftLeft(), a, b), ldt);
    }


    public Term buildUnsignedRightShiftExpression(Term a, Term b)
	    throws SLTranslationException {
	KeYJavaType resultType = null;

	try {
	    resultType = tc.getPromotedType(tc.getKeYJavaType(a), tc
		    .getKeYJavaType(b));
	} catch (RuntimeException e) {
	    raiseError("Error in unsigned shift-right expression "
		    + a.toString() + " >>> " + b.toString() + ".");
	}

	assert resultType != null;

	AbstractIntegerLDT ldt 
	    = (AbstractIntegerLDT) tc.getModelFor(resultType.getSort());
	return castToLDTSort(tb.func(ldt.getUnsignedShiftRight(), a, b), ldt);
    }


    public Term buildUnaryMinusExpression(Term a) throws SLTranslationException {
	KeYJavaType resultType = null;

	try {
	    resultType = tc.getPromotedType(tc.getKeYJavaType(a));
	} catch (RuntimeException e) {
	    raiseError("Error in unary minus expression -" + a.toString() + ".");
	}

	assert resultType != null;

        AbstractIntegerLDT ldt 
            = (AbstractIntegerLDT) tc.getModelFor(resultType.getSort());
	return castToLDTSort(tb.func(ldt.getNeg(), a), ldt);
    }


    public Term buildPromotedUnaryPlusExpression(Term a)
	    throws SLTranslationException {
	KeYJavaType resultType = null;

	try {
	    resultType = tc.getPromotedType(tc.getKeYJavaType(a));
	} catch (RuntimeException e) {
	    raiseError("Error in unary plus expression +" + a.toString() + ".");
	}

	assert resultType != null;

	AbstractIntegerLDT ldt 
	    = (AbstractIntegerLDT) tc.getModelFor(resultType.getSort());
	return castToLDTSort(a, ldt);
    }
}

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

    private final TypeConverter tc;
    private final Term trueLitTerm;
    private final Sort boolSort;


    public JavaIntegerSemanticsHelper(Services services) {
	assert services != null;

	this.tc = services.getTypeConverter();
	trueLitTerm = services.getTypeConverter().convertToLogicElement(
		BooleanLiteral.TRUE);
	boolSort = services.getJavaInfo().getKeYJavaType(
		PrimitiveType.JAVA_BOOLEAN).getSort();
    }


    private void raiseError(String message) throws SLTranslationException {
	throw new SLTranslationException(message);
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


    public Term castToJint(Term intTerm) {
	return tb.tf().createCastTerm(
		(AbstractSort) tc.getIntLDT().targetSort(), intTerm);
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

	return castToJint(tb.func(((AbstractIntegerLDT) tc
		.getModelFor(resultType.getSort())).getBitwiseOr(), a, b));
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

	return castToJint(tb.func(((AbstractIntegerLDT) tc
		.getModelFor(resultType.getSort())).getBitwiseAnd(), a, b));
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

	return castToJint(tb.func(((AbstractIntegerLDT) tc
		.getModelFor(resultType.getSort())).getBitwiseXor(), a, b));
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

	return castToJint(tb.func(((AbstractIntegerLDT) tc
		.getModelFor(resultType.getSort())).getBitwiseNegation(), a));
    }


    public Term buildAddExpression(Term a, Term b)
	    throws SLTranslationException {
	KeYJavaType resultType = null;

	try {
	    resultType = tc.getPromotedType(tc.getKeYJavaType(a), tc
		    .getKeYJavaType(b));
	} catch (RuntimeException e) {
	    raiseError("Error in additive expression " + a.toString() + " + "
		    + b.toString() + ".");
	}

	assert resultType != null;

	return castToJint(tb.func(((AbstractIntegerLDT) tc
		.getModelFor(resultType.getSort())).getAdd(), a, b));
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

	return castToJint(tb.func(((AbstractIntegerLDT) tc
		.getModelFor(resultType.getSort())).getSub(), a, b));
    }


    public Term buildMulExpression(Term a, Term b)
	    throws SLTranslationException {
	KeYJavaType resultType = null;

	try {
	    resultType = tc.getPromotedType(tc.getKeYJavaType(a), tc
		    .getKeYJavaType(b));
	} catch (RuntimeException e) {
	    raiseError("Error in additive expression " + a.toString() + " * "
		    + b.toString() + ".");
	}

	assert resultType != null;

	return castToJint(tb.func(((AbstractIntegerLDT) tc
		.getModelFor(resultType.getSort())).getMul(), a, b));
    }


    public Term buildDivExpression(Term a, Term b)
	    throws SLTranslationException {
	KeYJavaType resultType = null;

	try {
	    resultType = tc.getPromotedType(tc.getKeYJavaType(a), tc
		    .getKeYJavaType(b));
	} catch (RuntimeException e) {
	    raiseError("Error in additive expression " + a.toString() + " / "
		    + b.toString() + ".");
	}

	assert resultType != null;

	return castToJint(tb.func(((AbstractIntegerLDT) tc
		.getModelFor(resultType.getSort())).getDiv(), a, b));
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

	return castToJint(tb.func(((AbstractIntegerLDT) tc
		.getModelFor(resultType.getSort())).getMod(), a, b));
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

	return castToJint(tb.func(((AbstractIntegerLDT) tc
		.getModelFor(resultType.getSort())).getShiftRight(), a, b));
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

	return castToJint(tb.func(((AbstractIntegerLDT) tc
		.getModelFor(resultType.getSort())).getShiftLeft(), a, b));
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

	return castToJint(tb.func(((AbstractIntegerLDT) tc
		.getModelFor(resultType.getSort())).getUnsignedShiftRight(), a,
		b));
    }


    public Term buildUnaryMinusExpression(Term a) throws SLTranslationException {
	KeYJavaType resultType = null;

	try {
	    resultType = tc.getPromotedType(tc.getKeYJavaType(a));
	} catch (RuntimeException e) {
	    raiseError("Error in unary minus expression -" + a.toString() + ".");
	}

	assert resultType != null;

	return castToJint(tb.func(((AbstractIntegerLDT) tc
		.getModelFor(resultType.getSort())).getNeg(), a));
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

	return tb.tf().createCastTerm((AbstractSort) resultType.getSort(), a);
    }

}

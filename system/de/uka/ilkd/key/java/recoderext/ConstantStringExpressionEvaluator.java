package de.uka.ilkd.key.java.recoderext;

import recoder.CrossReferenceServiceConfiguration;
import recoder.abstraction.Type;
import recoder.java.Expression;
import recoder.java.NonTerminalProgramElement;
import recoder.java.ProgramElement;
import recoder.java.declaration.TypeDeclaration;
import recoder.java.expression.literal.NullLiteral;
import recoder.java.expression.literal.StringLiteral;
import recoder.service.ConstantEvaluator;

public class ConstantStringExpressionEvaluator extends RecoderModelTransformer {

    public ConstantStringExpressionEvaluator(
	    CrossReferenceServiceConfiguration services, TransformerCache cache) {
	super(services, cache);
    }

    private void evaluateConstantStringExpressions(NonTerminalProgramElement td) {
	for (int i = 0; i < td.getChildCount(); i++) {
	    ProgramElement pe = td.getChildAt(i);

	    if (pe instanceof Expression) {
		ConstantEvaluator cee = services.getConstantEvaluator();

		ConstantEvaluator.EvaluationResult res = new ConstantEvaluator.EvaluationResult();

		Type expType = services.getSourceInfo().getType((Expression) pe);

		if (!(pe instanceof NullLiteral) && expType != null
		        && expType.getFullName().equals("java.lang.String")) {
		    boolean isCTC = false;
		    try {
			isCTC = cee.isCompileTimeConstant((Expression) pe, res);			
		    } catch (java.lang.ArithmeticException t) {
			//
		    }
		    if (isCTC && res.getTypeCode() == ConstantEvaluator.STRING_TYPE) {
			replace(pe, new StringLiteral("\"" + res.getString()
			        + "\""));
			continue;
		    }
		}
	    }

	    if (pe instanceof NonTerminalProgramElement) {
		evaluateConstantStringExpressions((NonTerminalProgramElement) pe);
	    }
	}
    }

    @Override
    protected void makeExplicit(TypeDeclaration td) {
	evaluateConstantStringExpressions(td);
    }

}

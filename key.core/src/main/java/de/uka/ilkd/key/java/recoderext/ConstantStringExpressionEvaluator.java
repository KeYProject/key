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
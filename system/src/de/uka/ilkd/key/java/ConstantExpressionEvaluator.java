// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 


package de.uka.ilkd.key.java;

import recoder.java.JavaProgramFactory;
import recoder.service.ConstantEvaluator;
import recoder.service.DefaultConstantEvaluator;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.recoderext.KeYCrossReferenceServiceConfiguration;


public class ConstantExpressionEvaluator {

    private Services services = null;

    private ConstantEvaluator recCe = null;

    static final int BOOLEAN_TYPE = 0, BYTE_TYPE = 1,
	SHORT_TYPE = 2, CHAR_TYPE = 3, INT_TYPE = 4, LONG_TYPE = 5,
	FLOAT_TYPE = 6, DOUBLE_TYPE = 7, STRING_TYPE = 8;
    

    ConstantExpressionEvaluator(Services s) {
	services = s;
    }

    public Services getServices() {
	return services;
    }


    public boolean isCompileTimeConstant(Expression expr) {
	return getRecoderConstantEvaluator().
	    isCompileTimeConstant(parseExpression(expr));
	
    }
    
    public boolean isCompileTimeConstant(Expression expr, 
					 ConstantEvaluator.EvaluationResult result) {	
	return getRecoderConstantEvaluator().
	    isCompileTimeConstant(parseExpression(expr), result);
	
    }


    public KeYJavaType getCompileTimeConstantType(Expression expr) {	
	recoder.abstraction.Type javaType = getRecoderConstantEvaluator().
	    getCompileTimeConstantType(parseExpression(expr));
	return services.getJavaInfo().getKeYJavaType
	    (javaType.getFullName());
    }


    private ConstantEvaluator getRecoderConstantEvaluator() {
	if (recCe == null) {
	    KeYCrossReferenceServiceConfiguration servConf = 
		services.getJavaInfo().getKeYProgModelInfo().getServConf();
	    recCe = new DefaultConstantEvaluator(servConf);
	}
	return recCe;
    }


    private recoder.java.Expression parseExpression(Expression expr) {
	recoder.java.Expression recExpr = null;
	try {
	    recExpr = JavaProgramFactory.getInstance().
		parseExpression(expr.toString());
	} catch (recoder.ParserException exc) {
	    System.err.println("Failed to parse \n"+expr+
			       "\nas Java expression!");
	}
	return recExpr;
    }

}

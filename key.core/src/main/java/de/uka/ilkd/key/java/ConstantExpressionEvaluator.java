/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.recoderext.KeYCrossReferenceServiceConfiguration;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import recoder.java.JavaProgramFactory;
import recoder.service.ConstantEvaluator;
import recoder.service.DefaultConstantEvaluator;

public class ConstantExpressionEvaluator {

    private static final Logger LOGGER = LoggerFactory.getLogger(ConstantExpressionEvaluator.class);
    private Services services = null;

    private ConstantEvaluator recCe = null;

    static final int BOOLEAN_TYPE = 0, BYTE_TYPE = 1, SHORT_TYPE = 2, CHAR_TYPE = 3, INT_TYPE = 4,
            LONG_TYPE = 5, FLOAT_TYPE = 6, DOUBLE_TYPE = 7, STRING_TYPE = 8;


    ConstantExpressionEvaluator(Services s) {
        services = s;
    }

    public Services getServices() {
        return services;
    }


    public boolean isCompileTimeConstant(Expression expr) {
        return getRecoderConstantEvaluator().isCompileTimeConstant(parseExpression(expr));

    }

    public boolean isCompileTimeConstant(Expression expr,
            ConstantEvaluator.EvaluationResult result) {
        return getRecoderConstantEvaluator().isCompileTimeConstant(parseExpression(expr), result);

    }


    public KeYJavaType getCompileTimeConstantType(Expression expr) {
        recoder.abstraction.Type javaType =
            getRecoderConstantEvaluator().getCompileTimeConstantType(parseExpression(expr));
        return services.getJavaInfo().getKeYJavaType(javaType.getFullName());
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
            recExpr = JavaProgramFactory.getInstance().parseExpression(expr.toString());
        } catch (recoder.ParserException exc) {
            LOGGER.error("Failed to parse {} as Java expression!", expr);
        }
        return recExpr;
    }
}

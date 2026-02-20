/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
// Universitaet Koblenz-Landau, Germany
// Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
// Technical University Darmstadt, Germany
// Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.java.transformations.pipeline;

import java.util.Objects;

import de.uka.ilkd.key.java.transformations.ConstantExpressionEvaluator;
import de.uka.ilkd.key.java.transformations.EvaluationException;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.TypeDeclaration;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.visitor.VoidVisitorWithDefaults;

public class ConstantStringExpressionEvaluator extends JavaTransformer {

    public ConstantStringExpressionEvaluator(TransformationPipelineServices services) {
        super(services);
    }


    private void evaluateConstantStringExpressions(Node td) {
        td.accept(new VoidVisitorWithDefaults<>() {
            @Override
            public void defaultAction(Node n, Object arg) {
                if (n instanceof Expression) {
                    var e = (Expression) n;
                    ConstantExpressionEvaluator cee = services.getConstantEvaluator();
                    var expType = e.calculateResolvedType();
                    if (!e.isNullLiteralExpr() && expType != null
                            && expType.isReferenceType()
                            && Objects.equals(expType.asReferenceType().getQualifiedName(),
                                "java.lang.String")) {
                        try {
                            var expression = cee.evaluate(e);
                            e.replace(expression);
                        } catch (EvaluationException t) {
                            //
                        }
                    }
                }
            }
        }, null);
    }

    @Override
    public void apply(TypeDeclaration<?> td) {
        evaluateConstantStringExpressions(td);
    }
}

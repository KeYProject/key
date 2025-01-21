/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.parser.varcond;

import org.key_project.logic.SyntaxElement;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.rusty.Services;
import org.key_project.rusty.ast.expr.Expr;
import org.key_project.rusty.ast.expr.LabeledExpression;
import org.key_project.rusty.logic.op.sv.ProgramSV;
import org.key_project.rusty.rule.MatchConditions;
import org.key_project.rusty.rule.VariableCondition;


/**
 * Checks whether the given statement is labeled, i.e., actual a LabeledStatement. This information
 * is obtained from the program prefix.
 *
 * @author Dominic Steinhoefel
 */
public class IsLabeledCondition implements VariableCondition {
    private final boolean negated;
    private final ProgramSV exprSV;

    public IsLabeledCondition(ProgramSV exprSV, boolean negated) {
        this.negated = negated;
        this.exprSV = exprSV;
    }

    @Override
    public MatchConditions check(SchemaVariable var, SyntaxElement instCandidate,
            MatchConditions matchCond, Services services) {
        final var svInst = matchCond.getInstantiations();

        final var expr = (Expr) svInst.getInstantiation(exprSV);

        return negated == expr instanceof LabeledExpression ? null : matchCond;
    }
}

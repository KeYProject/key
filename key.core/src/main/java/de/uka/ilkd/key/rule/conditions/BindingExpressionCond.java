/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.rule.conditions;

import de.uka.ilkd.key.java.ast.expression.Expression;
import de.uka.ilkd.key.java.ast.statement.Guard;
import de.uka.ilkd.key.java.ast.statement.LoopStatement;
import de.uka.ilkd.key.java.visitor.BindingVariableVisitor;

import org.key_project.logic.LogicServices;
import org.key_project.logic.SyntaxElement;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.prover.rules.VariableCondition;
import org.key_project.prover.rules.instantiation.MatchResultInfo;
import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

/// This is a variable condition, that checks if a given variable binds new variables.
///
/// @author Alexander Weigl
/// @version 1 (20.08.26)
public class BindingExpressionCond implements VariableCondition {
    /// Is negated
    private final boolean negated;

    /// A schema variable representing a Java Expression.
    private final SchemaVariable svExpr;

    public BindingExpressionCond(SchemaVariable svExpr, boolean negated) {
        this.svExpr = svExpr;
        this.negated = negated;
    }

    @Override
    public String toString() {
        return (negated ? "\\not " : "") + "\\isBindingExpr(" + svExpr.name() + ")";
    }

    @Override
    public @Nullable MatchResultInfo check(
            @Nullable SchemaVariable var, @Nullable SyntaxElement instCandidate,
            @NonNull MatchResultInfo matchCond, @NonNull LogicServices services) {
        var newMatchCondition = matchCond;
        var svInst = (de.uka.ilkd.key.rule.inst.SVInstantiations) matchCond.getInstantiations();
        var condition = svInst.getInstantiation(svExpr);

        Expression expression = null;
        boolean isBindingExpr = false;

        if (condition instanceof Expression e) {
            expression = e;
        } else if (condition instanceof LoopStatement loop) {
            expression = loop.getGuardExpression();
        } else if (condition instanceof Guard guard) {
            expression = guard.getExpression();
        }

        if (expression != null) {
            isBindingExpr = BindingVariableVisitor.binds(expression);
        } else if (condition instanceof ImmutableList<?> list) {
            for (Object element : list) {
                if (element instanceof LoopStatement loop
                        && BindingVariableVisitor.binds(loop.getGuardExpression())) {
                    isBindingExpr = true;
                    break;
                }
            }
        }

        if (negated) {
            return isBindingExpr ? null : newMatchCondition;
        } else {
            return isBindingExpr ? newMatchCondition : null;
        }
    }
}

/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.rule.conditions;

import de.uka.ilkd.key.java.ast.expression.Expression;
import de.uka.ilkd.key.java.visitor.BindingVariableVisitor;

import org.key_project.logic.LogicServices;
import org.key_project.logic.SyntaxElement;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.prover.rules.VariableCondition;
import org.key_project.prover.rules.instantiation.MatchResultInfo;

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
    public @Nullable MatchResultInfo check(
            @Nullable SchemaVariable var, @Nullable SyntaxElement instCandidate,
            @NonNull MatchResultInfo matchCond, @NonNull LogicServices services) {
        var newMatchCondition = matchCond;
        var svInst = (de.uka.ilkd.key.rule.inst.SVInstantiations) matchCond.getInstantiations();
        var condition = svInst.getInstantiation(svExpr);

        boolean isBindingExpr = false;

        if (condition instanceof Expression e) {
            isBindingExpr = BindingVariableVisitor.binds(e);
        } else {
            newMatchCondition = null;
        }

        if (negated) {
            return isBindingExpr ? null : newMatchCondition;
        } else {
            return isBindingExpr ? newMatchCondition : null;
        }
    }
}

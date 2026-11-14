/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.rule.conditions;

import de.uka.ilkd.key.java.ast.Statement;
import de.uka.ilkd.key.java.ast.statement.LoopStatement;
import de.uka.ilkd.key.java.visitor.BindingVariableVisitor;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

import org.key_project.logic.LogicServices;
import org.key_project.logic.SyntaxElement;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.prover.rules.VariableCondition;
import org.key_project.prover.rules.instantiation.MatchResultInfo;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

/// Checks whether a loop statement has a guard that binds at least one pattern variable.
///
/// This is the loop counterpart of [BindingExpressionCond]. It accepts `while`, `for`, and `do`
/// statements and inspects their guard expression with [BindingVariableVisitor#binds].
///
/// @author Alexander Weigl
public final class IsBindingLoopCondition implements VariableCondition {
    private final SchemaVariable loopSV;

    /// @param loopSV the schema variable holding the loop statement
    public IsBindingLoopCondition(SchemaVariable loopSV) {
        this.loopSV = loopSV;
    }

    /// Returns whether the given statement is a loop whose guard binds a pattern variable.
    ///
    /// @param statement the statement to inspect
    /// @return true for a `while`, `for`, or `do` loop with a binding guard
    static boolean bindsLoop(Statement statement) {
        return statement instanceof LoopStatement loop
                && BindingVariableVisitor.binds(loop.getGuardExpression());
    }

    @Override
    public @Nullable MatchResultInfo check(@Nullable SchemaVariable var,
            @Nullable SyntaxElement instCandidate, @NonNull MatchResultInfo matchCond,
            @NonNull LogicServices services) {
        var svInst = (SVInstantiations) matchCond.getInstantiations();
        var statement = (Statement) svInst.getInstantiation(loopSV);
        return statement != null && bindsLoop(statement) ? matchCond : null;
    }

    @Override
    public String toString() {
        return "\\isBindingLoop(" + loopSV.name() + ")";
    }
}

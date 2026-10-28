/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.conditions;

import java.util.Map;

import de.uka.ilkd.key.java.ast.Statement;
import de.uka.ilkd.key.java.ast.declaration.LocalVariableDeclaration;
import de.uka.ilkd.key.java.ast.declaration.VariableSpecification;
import de.uka.ilkd.key.java.ast.expression.Expression;
import de.uka.ilkd.key.java.ast.reference.TypeRef;
import de.uka.ilkd.key.java.visitor.BindingVariableVisitor;
import de.uka.ilkd.key.logic.op.LocationVariable;

import org.key_project.logic.LogicServices;
import org.key_project.logic.SyntaxElement;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.prover.rules.VariableCondition;
import org.key_project.prover.rules.instantiation.MatchResultInfo;
import org.key_project.util.collection.ImmutableArray;

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
    /// A schema variable representing a program that binds variable under positive polarity of
    /// `svExpr`
    private final @Nullable SchemaVariable svPosBinding;
    /// Will store the update `{...||i := i_before||...}`.
    private final @Nullable SchemaVariable svNegBinding;

    public BindingExpressionCond(SchemaVariable svExpr, boolean negated) {
        this(svExpr, null, null, negated);
    }

    public BindingExpressionCond(SchemaVariable svExpr, @Nullable SchemaVariable svPosBinding,
            @Nullable SchemaVariable svNegBinding,
            boolean negated) {
        this.svExpr = svExpr;
        this.svPosBinding = svPosBinding;
        this.svNegBinding = svNegBinding;
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
            var v = BindingVariableVisitor.analyze(e);
            isBindingExpr = !(v.whenFalse().isEmpty() && v.whenTrue().isEmpty());
            // b ? v.whenTrue() : v.whenFalse()

            if (isBindingExpr && svPosBinding != null && svNegBinding != null) {
                svInst = svInst
                        .add(svPosBinding, createBinders(v.whenTrue()), Statement.class, services)
                        .add(svNegBinding, createBinders(v.whenFalse()), Statement.class, services);
                newMatchCondition = newMatchCondition.setInstantiations(svInst);
            }
        } else {
            newMatchCondition = null;
        }


        if (negated) {
            return isBindingExpr ? null : newMatchCondition;
        } else {
            return isBindingExpr ? newMatchCondition : null;
        }
    }

    private ImmutableArray<Statement> createBinders(Map<LocationVariable, Expression> variables) {

        var seq = variables.entrySet().stream().map(
            it -> {
                final var key = it.getKey();
                final var value = it.getValue();
                return new LocalVariableDeclaration(
                    new TypeRef(key.getKeYJavaType()),
                    new VariableSpecification(key, value, key.getKeYJavaType()));
            })
                .toArray(Statement[]::new);
        return new ImmutableArray<>(seq);
        // return new StatementBlock(new ImmutableArray<>(seq));
    }
}

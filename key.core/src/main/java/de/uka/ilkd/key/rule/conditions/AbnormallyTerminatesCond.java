/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.conditions;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.Statement;

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
public class AbnormallyTerminatesCond implements VariableCondition {
    /// Is negated
    private final boolean negated;

    /// A schema variable representing a Java Expression.
    private final SchemaVariable svStmts;

    public AbnormallyTerminatesCond(SchemaVariable svStmts, boolean negated) {
        this.svStmts = svStmts;
        this.negated = negated;
    }

    @Override
    public @Nullable MatchResultInfo check(
            @Nullable SchemaVariable var, @Nullable SyntaxElement instCandidate,
            @NonNull MatchResultInfo matchCond, @NonNull LogicServices services) {
        var svInst = (de.uka.ilkd.key.rule.inst.SVInstantiations) matchCond.getInstantiations();
        var s = svInst.getInstantiation(svStmts);
        boolean isAbnormallyTerminating = false;

        var analysis = new AlwaysAbnormallyTerminatingAnalysis(null, (Services) services);
        if (s instanceof ImmutableArray<?> stmts) {

        } else if (s instanceof Statement stmts) {

        } else {
            matchCond = null;
        }


        if (negated) {
            return isAbnormallyTerminating ? null : matchCond;
        } else {
            return isAbnormallyTerminating ? matchCond : null;
        }
    }
}

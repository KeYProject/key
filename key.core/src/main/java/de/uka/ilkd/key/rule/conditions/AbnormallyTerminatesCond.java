/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
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

/// Checks whether a given program statement (or list of statements) cannot complete normally,
/// i.e. whether control never falls through past it. See
/// [AlwaysAbnormallyTerminatingAnalysis] for the exact semantics.
///
/// @author Alexander Weigl
/// @version 1 (20.08.26)
public class AbnormallyTerminatesCond implements VariableCondition {
    /// Is negated
    private final boolean negated;

    /// A schema variable representing a Java statement or statement list.
    private final SchemaVariable svStmts;

    public AbnormallyTerminatesCond(SchemaVariable svStmts, boolean negated) {
        this.svStmts = svStmts;
        this.negated = negated;
    }

    @Override
    public String toString() {
        return (negated ? "\\not " : "") + "\\alwaysAbnormallyTerminates(" + svStmts.name() + ")";
    }

    @Override
    public @Nullable MatchResultInfo check(
            @Nullable SchemaVariable var, @Nullable SyntaxElement instCandidate,
            @NonNull MatchResultInfo matchCond, @NonNull LogicServices services) {
        var svInst = (de.uka.ilkd.key.rule.inst.SVInstantiations) matchCond.getInstantiations();
        var instantiation = svInst.getInstantiation(svStmts);
        var analysis = new AlwaysAbnormallyTerminatingAnalysis((Services) services);

        final boolean aborts;
        if (instantiation instanceof ImmutableArray<?> stmts) {
            aborts = analysis.isAlwaysAbnormallyTerminating(stmts);
        } else if (instantiation instanceof Statement stmt) {
            aborts = analysis.isAlwaysAbnormallyTerminating(stmt);
        } else {
            return null;
        }

        return negated != aborts ? matchCond : null;
    }
}

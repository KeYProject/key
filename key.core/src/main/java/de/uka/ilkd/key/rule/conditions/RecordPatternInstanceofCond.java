/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.rule.conditions;

import de.uka.ilkd.key.java.ast.expression.Expression;
import de.uka.ilkd.key.java.ast.expression.operator.InstanceofPattern;
import de.uka.ilkd.key.java.ast.pattern.RecordPattern;

import org.key_project.logic.LogicServices;
import org.key_project.logic.SyntaxElement;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.prover.rules.VariableCondition;
import org.key_project.prover.rules.instantiation.MatchResultInfo;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

/**
 * This is a variable condition that checks whether a given expression is an {@code instanceof}
 * expression with a record pattern.
 *
 * @author Alexander Weigl
 * @version 1 (20.08.26)
 */
public class RecordPatternInstanceofCond implements VariableCondition {
    /** Is negated */
    private final boolean negated;

    /** A schema variable representing a Java Expression. */
    private final SchemaVariable svExpr;

    public RecordPatternInstanceofCond(SchemaVariable svExpr, boolean negated) {
        this.svExpr = svExpr;
        this.negated = negated;
    }

    @Override
    public String toString() {
        return (negated ? "\\not " : "") + "\\isRecordPatternInstanceof(" + svExpr.name() + ")";
    }

    @Override
    public @Nullable MatchResultInfo check(
            @Nullable SchemaVariable var, @Nullable SyntaxElement instCandidate,
            @NonNull MatchResultInfo matchCond, @NonNull LogicServices services) {
        var svInst = (de.uka.ilkd.key.rule.inst.SVInstantiations) matchCond.getInstantiations();
        var condition = svInst.getInstantiation(svExpr);

        if (!(condition instanceof Expression)) {
            return null;
        }
        boolean isRecordPattern = condition instanceof InstanceofPattern instanceofPattern
                && instanceofPattern.getPattern() instanceof RecordPattern;

        if (negated) {
            return isRecordPattern ? null : matchCond;
        } else {
            return isRecordPattern ? matchCond : null;
        }
    }
}

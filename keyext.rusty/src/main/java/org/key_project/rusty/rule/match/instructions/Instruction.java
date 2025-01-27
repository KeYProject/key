/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.rule.match.instructions;

import org.key_project.logic.LogicServices;
import org.key_project.logic.Term;
import org.key_project.logic.op.Operator;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.prover.rules.MatchConditions;
import org.key_project.rusty.Services;
import org.key_project.rusty.ast.RustyProgramElement;
import org.key_project.rusty.logic.SVPlace;
import org.key_project.rusty.logic.op.ElementaryUpdate;
import org.key_project.rusty.logic.op.Modality;
import org.key_project.rusty.logic.op.sv.*;

import org.jspecify.annotations.NonNull;

public abstract class Instruction<Op extends Operator> implements MatchInstruction {
    public static Instruction<@NonNull Operator> matchOp(Operator op) {
        return new MatchOpIdentityInstruction<>(op);
    }

    // public static Instruction<SortDependingFunction> matchSortDependingFunction(
    // SortDependingFunction op) {
    // return new MatchSortDependingFunctionInstruction(op);
    // }

    public static MatchModalOperatorSVInstruction matchModalOperatorSV(
            ModalOperatorSV sv) {
        return new MatchModalOperatorSVInstruction(sv);
    }

    public static MatchModalityKindInstruction matchModalOperator(Modality mod) {
        return new MatchModalityKindInstruction(mod.kind());
    }

    public static MatchSchemaVariableInstruction<? extends org.key_project.logic.op.sv.SchemaVariable> matchFormulaSV(
            FormulaSV sv) {
        return new MatchFormulaSVInstruction(sv);
    }

    public static MatchSchemaVariableInstruction<? extends org.key_project.logic.op.sv.SchemaVariable> matchTermSV(
            TermSV sv) {
        return new MatchTermSVInstruction(sv);
    }

    public static MatchSchemaVariableInstruction<? extends org.key_project.logic.op.sv.SchemaVariable> matchVariableSV(
            VariableSV sv) {
        return new MatchVariableSVInstruction(sv);
    }

    public static MatchSchemaVariableInstruction<? extends org.key_project.logic.op.sv.SchemaVariable> matchProgramSV(
            ProgramSV sv) {
        return new MatchProgramSVInstruction(sv);
    }

    public static MatchSchemaVariableInstruction<? extends SchemaVariable> matchUpdateSV(
            UpdateSV sv) {
        return new MatchUpdateSVInstruction(sv);
    }

    public static MatchInstruction matchProgram(RustyProgramElement prg) {
        return new MatchProgramInstruction(prg);
    }

    public static MatchInstruction matchAndBindVariable(
            QuantifiableVariable var) {
        return BindVariablesInstruction.create(var);
    }

    public static MatchInstruction matchElementaryUpdate(ElementaryUpdate elementaryUpdate) {
        return new MatchElementaryUpdateInstruction(elementaryUpdate);
    }

    public static MatchInstruction matchPlaceSV(SVPlace sv) {
        return new MatchPlaceSVInstruction(sv);
    }

    protected final Op op;

    protected Instruction(Op op) {
        this.op = op;
    }

    /**
     * tries to match the schema variable of this instruction with the specified {@link Term}
     * {@code instantiationCandidate} w.r.t. the given constraints by {@link MatchConditions}
     *
     * @param instantiationCandidate the {@link Term} to be matched
     * @param matchCond the {@link MatchConditions} with additional constraints (e.g. previous
     *        matches of this schemavariable)
     * @param services the {@link Services}
     * @return {@code null} if no matches have been found or the new {@link MatchConditions} with
     *         the pair {@code (sv, instantiationCandidate)} added
     */
    public abstract MatchConditions match(Term instantiationCandidate,
            MatchConditions matchCond,
            LogicServices services);
}

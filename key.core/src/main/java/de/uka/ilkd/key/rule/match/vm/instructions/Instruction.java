/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.match.vm.instructions;

import de.uka.ilkd.key.java.JavaProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.rule.MatchConditions;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;
import org.key_project.util.collection.ImmutableArray;

/** Class encoding the instructions of the matching vm */
public abstract class Instruction<OP extends Operator> implements MatchInstruction {

    public static @NonNull Instruction<Operator> matchOp(@NonNull Operator op) {
        return new MatchOpIdentityInstruction<>(op);
    }

    public static @NonNull Instruction<SortDependingFunction> matchSortDependingFunction(
            @NonNull SortDependingFunction op) {
        return new MatchSortDependingFunctionInstruction(op);
    }

    public static @NonNull MatchModalOperatorSVInstruction matchModalOperatorSV(
            ModalOperatorSV sv) {
        return new MatchModalOperatorSVInstruction(sv);
    }

    public static @NonNull MatchModalityInstruction matchModalOperator(@NonNull Modality mod) {
        return new MatchModalityInstruction(mod);
    }

    public static @NonNull MatchSchemaVariableInstruction<? extends SchemaVariable> matchFormulaSV(
            FormulaSV sv) {
        return new MatchFormulaSVInstruction(sv);
    }

    public static @NonNull MatchSchemaVariableInstruction<? extends SchemaVariable> matchTermSV(TermSV sv) {
        return new MatchTermSVInstruction(sv);
    }

    public static @NonNull MatchSchemaVariableInstruction<? extends SchemaVariable> matchVariableSV(
            VariableSV sv) {
        return new MatchVariableSVInstruction(sv);
    }

    public static @NonNull MatchSchemaVariableInstruction<? extends SchemaVariable> matchProgramSV(
            ProgramSV sv) {
        return new MatchProgramSVInstruction(sv);
    }

    public static @NonNull MatchSchemaVariableInstruction<? extends SchemaVariable> matchUpdateSV(
            UpdateSV sv) {
        return new MatchUpdateSVInstruction(sv);
    }

    public static @NonNull MatchInstruction matchTermLabelSV(ImmutableArray<TermLabel> labels) {
        return new MatchTermLabelInstruction(labels);
    }

    public static @NonNull MatchInstruction matchProgram(JavaProgramElement prg) {
        return new MatchProgramInstruction(prg);
    }

    public static @NonNull MatchInstruction matchAndBindVariables(
            @NonNull ImmutableArray<QuantifiableVariable> boundVars) {
        return new BindVariablesInstruction(boundVars);
    }

    public static @NonNull MatchInstruction unbindVariables(ImmutableArray<QuantifiableVariable> boundVars) {
        return new UnbindVariablesInstruction();
    }

    public static @NonNull MatchInstruction matchElementaryUpdate(@NonNull ElementaryUpdate elementaryUpdate) {
        return new MatchElementaryUpdateInstruction(elementaryUpdate);
    }

    protected final @NonNull OP op;

    protected Instruction(@NonNull OP op) {
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
    public abstract @Nullable MatchConditions match(Term instantiationCandidate, MatchConditions matchCond,
                                                    Services services);
}

/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.match.vm.instructions;

import de.uka.ilkd.key.java.JavaProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.rule.MatchConditions;

import org.key_project.logic.LogicServices;
import org.key_project.logic.op.Modality;
import org.key_project.logic.op.Operator;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.util.collection.ImmutableArray;

/** Class encoding the instructions of the matching vm */
public abstract class Instruction<OP extends Operator>
        implements MatchInstruction {

    public static Instruction<Operator> matchOp(Operator op) {
        return new MatchOpIdentityInstruction<>(op);
    }

    public static Instruction<SortDependingFunction> matchSortDependingFunction(
            SortDependingFunction op) {
        return new MatchSortDependingFunctionInstruction(op);
    }

    public static MatchModalOperatorSVInstruction matchModalOperatorSV(
            ModalOperatorSV sv) {
        return new MatchModalOperatorSVInstruction(sv);
    }

    public static MatchModalityInstruction matchModalOperator(Modality mod) {
        return new MatchModalityInstruction(mod);
    }

    public static MatchSchemaVariableInstruction<? extends SchemaVariable> matchFormulaSV(
            FormulaSV sv) {
        return new MatchFormulaSVInstruction(sv);
    }

    public static MatchSchemaVariableInstruction<? extends SchemaVariable> matchTermSV(TermSV sv) {
        return new MatchTermSVInstruction(sv);
    }

    public static MatchSchemaVariableInstruction<? extends SchemaVariable> matchVariableSV(
            VariableSV sv) {
        return new MatchVariableSVInstruction(sv);
    }

    public static MatchSchemaVariableInstruction<? extends SchemaVariable> matchProgramSV(
            ProgramSV sv) {
        return new MatchProgramSVInstruction(sv);
    }

    public static MatchSchemaVariableInstruction<? extends SchemaVariable> matchUpdateSV(
            UpdateSV sv) {
        return new MatchUpdateSVInstruction(sv);
    }

    public static MatchInstruction matchTermLabelSV(ImmutableArray<TermLabel> labels) {
        return new MatchTermLabelInstruction(labels);
    }

    public static MatchInstruction matchProgram(JavaProgramElement prg) {
        return new MatchProgramInstruction(prg);
    }

    public static MatchInstruction matchAndBindVariables(
            ImmutableArray<QuantifiableVariable> boundVars) {
        return new BindVariablesInstruction(boundVars);
    }

    public static MatchInstruction unbindVariables(
            ImmutableArray<QuantifiableVariable> boundVars) {
        return new UnbindVariablesInstruction();
    }

    public static MatchInstruction matchElementaryUpdate(ElementaryUpdate elementaryUpdate) {
        return new MatchElementaryUpdateInstruction(elementaryUpdate);
    }

    protected final OP op;

    protected Instruction(OP op) {
        this.op = op;
    }

    /**
     * tries to match the schema variable of this instruction with the specified {@link JTerm}
     * {@code instantiationCandidate} w.r.t. the given constraints by {@link MatchConditions}
     *
     * @param instantiationCandidate the {@link JTerm} to be matched
     * @param matchCond the {@link MatchConditions} with additional constraints (e.g. previous
     *        matches of this schemavariable)
     * @param services the {@link Services}
     * @return {@code null} if no matches have been found or the new {@link MatchConditions} with
     *         the pair {@code (sv, instantiationCandidate)} added
     */
    public abstract MatchConditions match(JTerm instantiationCandidate, MatchConditions matchCond,
            LogicServices services);
}

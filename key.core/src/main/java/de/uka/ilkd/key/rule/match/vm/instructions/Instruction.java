/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.match.vm.instructions;

import de.uka.ilkd.key.java.JavaProgramElement;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.op.*;

import org.key_project.util.collection.ImmutableArray;

import org.jspecify.annotations.NonNull;

/** Class encoding the instructions of the matching vm */
public abstract class Instruction<@NonNull OP extends org.key_project.logic.op.Operator>
        implements MatchInstruction {

    public static MatchModalOperatorSVInstruction matchModalOperatorSV(
            ModalOperatorSV sv) {
        return new MatchModalOperatorSVInstruction(sv);
    }

    public static MatchSchemaVariableInstruction matchNonVariableSV(OperatorSV sv) {
        return new MatchNonVariableSVInstruction(sv);
    }

    public static MatchSchemaVariableInstruction matchVariableSV(
            VariableSV sv) {
        return new MatchVariableSVInstruction(sv);
    }

    public static MatchSchemaVariableInstruction matchProgramSV(
            ProgramSV sv) {
        return new MatchProgramSVInstruction(sv);
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

    public static MatchInstruction unbindVariables(ImmutableArray<QuantifiableVariable> boundVars) {
        return new UnbindVariablesInstruction();
    }

    protected final OP op;

    protected Instruction(OP op) {
        this.op = op;
    }

}

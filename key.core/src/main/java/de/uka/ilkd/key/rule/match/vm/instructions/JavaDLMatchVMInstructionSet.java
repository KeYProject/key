/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.match.vm.instructions;

import de.uka.ilkd.key.java.JavaProgramElement;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.GenericSort;

import org.key_project.logic.SyntaxElement;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.logic.op.sv.OperatorSV;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.prover.rules.matcher.vm.instruction.CheckNodeKindInstruction;
import org.key_project.prover.rules.matcher.vm.instruction.GotoNextInstruction;
import org.key_project.prover.rules.matcher.vm.instruction.GotoNextSiblingInstruction;
import org.key_project.prover.rules.matcher.vm.instruction.MatchIdentityInstruction;
import org.key_project.prover.rules.matcher.vm.instruction.MatchInstruction;
import org.key_project.prover.rules.matcher.vm.instruction.VMInstruction;
import org.key_project.util.collection.ImmutableArray;

/** Class encoding the instructions of the matching vm */
public final class JavaDLMatchVMInstructionSet {

    public static GotoNextInstruction gotoNextInstruction() {
        return GotoNextInstruction.INSTANCE;
    }

    public static GotoNextSiblingInstruction gotoNextSiblingInstruction() {
        return GotoNextSiblingInstruction.INSTANCE;
    }

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

    public static VMInstruction unbindVariables(ImmutableArray<QuantifiableVariable> boundVars) {
        return new UnbindVariablesInstruction();
    }

    /**
     * returns the instruction for the specified variable
     *
     * @param op the {@link SchemaVariable} for which to get the instruction
     * @return the instruction for the specified variable
     */
    public static MatchSchemaVariableInstruction getMatchInstructionForSV(
            SchemaVariable op) {
        MatchSchemaVariableInstruction instruction;
        if (op instanceof VariableSV variableSV) {
            instruction = matchVariableSV(variableSV);
        } else if (op instanceof ProgramSV programSV) {
            instruction = matchProgramSV(programSV);
        } else if (op instanceof OperatorSV) {
            instruction = matchNonVariableSV((OperatorSV) op);
        } else {
            throw new IllegalArgumentException(
                "Do not know how to match " + op + " of type " + op.getClass());
        }
        return instruction;
    }

    public static SimilarSortDependingFunctionInstruction getSimilarSortDependingFunctionInstruction(
            SortDependingFunction sortDependingFunction) {
        return new SimilarSortDependingFunctionInstruction(sortDependingFunction);
    }

    public static MatchIdentityInstruction getMatchIdentityInstruction(
            SyntaxElement syntaxElement) {
        return new MatchIdentityInstruction(syntaxElement);
    }

    public static MatchGenericSortInstruction getMatchGenericSortInstruction(GenericSort gs) {
        return new MatchGenericSortInstruction(gs);
    }

    public static CheckNodeKindInstruction getCheckNodeKindInstruction(
            Class<? extends SyntaxElement> kind) {
        return new CheckNodeKindInstruction(kind);
    }
}

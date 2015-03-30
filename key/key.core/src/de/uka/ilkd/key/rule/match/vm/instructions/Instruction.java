package de.uka.ilkd.key.rule.match.vm.instructions;

import org.key_project.util.collection.ImmutableArray;

import de.uka.ilkd.key.java.JavaProgramElement;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.op.FormulaSV;
import de.uka.ilkd.key.logic.op.ModalOperatorSV;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.SortDependingFunction;
import de.uka.ilkd.key.logic.op.TermSV;
import de.uka.ilkd.key.logic.op.UpdateSV;
import de.uka.ilkd.key.logic.op.VariableSV;

/** enum encoding the instructions of the matching vm */
public abstract class Instruction<OP extends Operator> implements IMatchInstruction {

    public static Instruction<Operator> matchOp(Operator op) {
        return new MatchOpIdentityInstr(op);
    }

    public static Instruction<SortDependingFunction> matchSortDependingFunction(
            SortDependingFunction op) {
        return new MatchSortDependingFunctionInstr(op);
    }

    public static Instruction<ModalOperatorSV> matchModalOperatorSV(
            ModalOperatorSV sv) {
        return new MatchModalOperatorSVInstruction(sv);
    }

    public static Instruction<FormulaSV> matchFormulaSV(FormulaSV sv) {
        return new MatchFormulaSVInstruction(sv);
    }

    public static Instruction<TermSV> matchTermSV(TermSV sv) {
        return new MatchTermSVInstruction(sv);
    }

    public static Instruction<VariableSV> matchVariableSV(VariableSV sv) {
        return new MatchVariableSVInstr(sv);
    }

    public static Instruction<ProgramSV> matchProgramSV(ProgramSV sv) {
        return new MatchProgramSVInstruction(sv);
    }

    public static Instruction<UpdateSV> matchUpdateSV(UpdateSV sv) {
        return new MatchUpdateSVInstruction(sv);
    }

    public static IMatchInstruction matchTermLabelSV(ImmutableArray<TermLabel> labels) {
        return new MatchTermLabelInstruction(labels);
    }

    public static IMatchInstruction matchProgram(JavaProgramElement prg) {
        return new MatchProgramInstruction(prg);
    }

    public static IMatchInstruction matchAndBindVariables(ImmutableArray<QuantifiableVariable> boundVars) {
        return new BindVariables(boundVars);
    }

    public static IMatchInstruction unbindVariables(ImmutableArray<QuantifiableVariable> boundVars) {
        return new UnbindVariables();
    }


    protected final OP op;

    protected Instruction(OP op) {
        this.op = op;
    }


}
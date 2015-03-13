package de.uka.ilkd.key.rule.match.vm;

import org.key_project.util.collection.ImmutableArray;

import de.uka.ilkd.key.java.JavaProgramElement;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.op.FormulaSV;
import de.uka.ilkd.key.logic.op.ModalOperatorSV;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.SortDependingFunction;
import de.uka.ilkd.key.logic.op.TermLabelSV;
import de.uka.ilkd.key.logic.op.TermSV;
import de.uka.ilkd.key.logic.op.UpdateSV;
import de.uka.ilkd.key.logic.op.VariableSV;
import de.uka.ilkd.key.rule.MatchConditions;

/** enum encoding the instructions of the matching vm */
public abstract class Instruction<OP extends Operator> implements IMatchInstruction<OP> {

   public static Instruction<Operator> matchOp(Operator op) {
      return new MatchOpIdentityInstr(op);
   }

   public static Instruction<SortDependingFunction> matchSortDependingFunction(
         SortDependingFunction op) {
      return new MatchSortDependingFunctionInstr(op);
   }

   public static Instruction<ModalOperatorSV> matchModalOperatorSV(ModalOperatorSV sv) {
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

   public static Instruction<TermLabelSV> matchTermLabelSV(TermLabelSV sv) {
      return new MatchTermLabelSVInstruction(sv);
   }

   public static IMatchInstruction<ProgramElement> matchProgram(JavaProgramElement prg) {
      return new MatchProgramInstruction(prg);
   }

   protected final OP op;

   protected Instruction(OP op) {
      this.op = op;
   }

   public abstract MatchConditions match(Operator p_op, MatchConditions mc, Services services);

   public static IMatchInstruction matchAndBindVariables(
         ImmutableArray<QuantifiableVariable> boundVars) {
      return null;
   }

   public static IMatchInstruction unbindVariables(
         ImmutableArray<QuantifiableVariable> boundVars) {
      return null;
   }

}
package de.uka.ilkd.key.rule.match.vm;

import org.key_project.util.collection.ImmutableArray;

import de.uka.ilkd.key.java.ContextStatementBlock;
import de.uka.ilkd.key.java.JavaProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.FormulaSV;
import de.uka.ilkd.key.logic.op.ModalOperatorSV;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.SortDependingFunction;
import de.uka.ilkd.key.logic.op.TermLabelSV;
import de.uka.ilkd.key.logic.op.TermSV;
import de.uka.ilkd.key.logic.op.UpdateSV;
import de.uka.ilkd.key.logic.op.VariableSV;
import de.uka.ilkd.key.rule.IfFormulaInstantiation;
import de.uka.ilkd.key.rule.IfMatchResult;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.TacletMatcher;

public class VMTacletMatcher implements TacletMatcher {

   private IMatchInstruction[] program = new IMatchInstruction[100];
   
   protected void createProgram(Term pattern, int instrPtr) {
      final Operator op = pattern.op();

      final JavaProgramElement patternPrg = pattern.javaBlock().program();

      if (!pattern.javaBlock().isEmpty() || patternPrg instanceof ContextStatementBlock) {
         program[instrPtr] = Instruction.matchProgram(patternPrg);
         ++instrPtr;
      }
      
      final ImmutableArray<QuantifiableVariable> boundVars = pattern.boundVars();     
      if (!boundVars.isEmpty()) {
         program[instrPtr] = Instruction.matchAndBindVariables(boundVars);
         ++instrPtr;
      }
      
      if (op instanceof SchemaVariable) {
         if (op instanceof ModalOperatorSV) {
            program[instrPtr] = Instruction.matchModalOperatorSV((ModalOperatorSV) op);
         } else if (op instanceof FormulaSV) {
            program[instrPtr] = Instruction.matchFormulaSV((FormulaSV)op);
         } else if (op instanceof TermSV) {
            program[instrPtr] = Instruction.matchTermSV((TermSV)op);
         } else if (op instanceof VariableSV) {
            program[instrPtr] = Instruction.matchVariableSV((VariableSV)op);
         } else if (op instanceof ProgramSV) {
            program[instrPtr] = Instruction.matchProgramSV((ProgramSV)op);
         } else if (op instanceof UpdateSV) {
            program[instrPtr] = Instruction.matchUpdateSV((UpdateSV)op);
         } else if (op instanceof TermLabelSV) {
            program[instrPtr] = Instruction.matchTermLabelSV((TermLabelSV)op);
         } else {
            throw new IllegalArgumentException("Do not know how to match " + op + 
                  " of type " + op.getClass());
         }
      } else if (op instanceof SortDependingFunction) {
         program[instrPtr] = Instruction.matchSortDependingFunction((SortDependingFunction)op); 
      } else {
         program[instrPtr] = Instruction.matchOp(op);
      }

      ++instrPtr;
      for (int i = 0; i < pattern.arity(); i++) {
         createProgram(pattern.sub(i), instrPtr);
      }
      
      if (!boundVars.isEmpty()) {
         program[instrPtr] = Instruction.unbindVariables(boundVars);
         ++instrPtr;
      }

   }


   
   
   @Override
   public IfMatchResult matchIf(Iterable<IfFormulaInstantiation> p_toMatch,
         Term p_template, MatchConditions p_matchCond, Services p_services) {
      return null;
   }

   @Override
   public MatchConditions matchIf(Iterable<IfFormulaInstantiation> p_toMatch,
         MatchConditions p_matchCond, Services p_services) {
      return null;
   }

   @Override
   public MatchConditions checkConditions(MatchConditions p_matchconditions,
         Services services) {
      return null;
   }

   @Override
   public MatchConditions checkVariableConditions(SchemaVariable var,
         SVSubstitute instantiationCandidate, MatchConditions matchCond,
         Services services) {
      return null;
   }

   @Override
   public MatchConditions matchFind(Term term, MatchConditions matchCond,
         Services services) {
      return null;
   }
   
}

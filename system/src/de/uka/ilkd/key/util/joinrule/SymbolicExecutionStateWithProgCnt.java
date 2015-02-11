package de.uka.ilkd.key.util.joinrule;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.util.Triple;

/**
 * A symbolic execution state with program counter is a triple
 * of a symbolic state in form of a parallel update, a path
 * condition in form of a JavaDL formula, and a program counter
 * in form of a JavaDL formula with non-empty Java Block (and a
 * possible post condition as first, and only, sub term).
 * 
 * @author Dominic Scheurer
 */
public class SymbolicExecutionStateWithProgCnt extends Triple<Term, Term, Term> {

   private Goal correspondingGoal = null;
   
   /**
    * @param symbolicState The symbolic state (parallel update).
    * @param pathCondition The path condition (formula).
    * @param programCounter The program counter: Formula with non-empty
    *    Java block and post condition as only sub term.
    */
   public SymbolicExecutionStateWithProgCnt(
         Term symbolicState, Term pathCondition, Term programCounter) {
      super(symbolicState, pathCondition, programCounter);
   }
   
   /**
    * @param symbolicState The symbolic state (parallel update).
    * @param pathCondition The path condition (formula).
    * @param programCounter The program counter: Formula with non-empty
    *    Java block and post condition as only sub term.
    * @param correspondingGoal The goal corresponding to this SE state.
    */
   public SymbolicExecutionStateWithProgCnt(
         Term symbolicState, Term pathCondition, Term programCounter, Goal correspondingGoal) {
      this(symbolicState, pathCondition, programCounter);
      this.correspondingGoal = correspondingGoal;
   }
   
   /**
    * @return The symbolic state.
    */
   public Term getSymbolicState() {
      return first;
   }
   
   /**
    * @return The path condition.
    */
   public Term getPathCondition() {
      return second;
   }
   
   /**
    * @return The program counter (and post condition).
    */
   public Term getProgramCounter() {
      return third;
   }
   
   /**
    * @return The goal corresponding to this SE state.
    */
   public Goal getCorrespondingGoal() {
      return correspondingGoal;
   }
   
}

package de.uka.ilkd.key.util.joinrule;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.util.Pair;

/**
 * A symbolic execution state is a pair of a symbolic state in
 * form of a parallel update, and a path condition in form of
 * a JavaDL formula.
 * 
 * @author Dominic Scheurer
 */
public class SymbolicExecutionState extends Pair<Term, Term> {

   private Goal correspondingGoal = null;

   /**
    * @param symbolicState The symbolic state (parallel update).
    * @param pathCondition The path condition (formula).
    */
   public SymbolicExecutionState(Term symbolicState, Term pathCondition) {
      super(symbolicState, pathCondition);
   }
   
   /**
    * @param symbolicState The symbolic state (parallel update).
    * @param pathCondition The path condition (formula).
    * @param correspondingGoal The goal corresponding to this SE state.
    */
   public SymbolicExecutionState(
         Term symbolicState, Term pathCondition, Goal correspondingGoal) {
      this(symbolicState, pathCondition);
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
    * @return The goal corresponding to this SE state.
    */
   public Goal getCorrespondingGoal() {
      return correspondingGoal;
   }
   
}

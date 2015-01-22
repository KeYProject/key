package de.uka.ilkd.key.util.joinrule;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.util.Pair;

/**
 * A symbolic execution state is a pair of a symbolic state in
 * form of a parallel update, and a path condition in form of
 * a JavaDL formula.
 * 
 * @author Dominic Scheurer
 */
public class SymbolicExecutionState extends Pair<Term, Term> {

   /**
    * @param symbolicState The symbolic state (parallel update).
    * @param pathCondition The path condition (formula).
    */
   public SymbolicExecutionState(Term symbolicState, Term pathCondition) {
      super(symbolicState, pathCondition);
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
   
}

package de.uka.ilkd.key.rule.join;

import java.util.HashSet;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.util.Pair;
import de.uka.ilkd.key.util.joinrule.SymbolicExecutionState;

/**
 * Defines a concrete join procedure, in particular the result
 * of joining two terms for a given location variable in two
 * Symbolic Execution states.<p>
 * 
 * For example, computing the join result for a variable x in
 * one state where x is 42 and another one where x is 17, the
 * result could be the update x := c, where c is constrained to
 * be positive by a formula in the returned constraints set.<p>
 * 
 * New join procedures need to be registered in the list CONCRETE_RULES!
 * 
 * @author Dominic Scheurer
 * 
 * @see JoinIfThenElse
 * @see JoinIfThenElseAntecedent
 * @see JoinWeaken
 * @see JoinWithSignLattice
 */
public abstract class JoinProcedure {
    
    /** Concrete join procedures. */
    public static final ImmutableList<JoinProcedure> CONCRETE_RULES =
            ImmutableSLList.<JoinProcedure>nil()
                .append(JoinIfThenElse.INSTANCE)
                .append(JoinIfThenElseAntecedent.INSTANCE)
                .append(JoinWithSignLattice.INSTANCE)
                .append(JoinWeaken.INSTANCE);

		/**
	    * Joins two values valueInState1 and valueInState2 of corresponding
	    * SE states state1 and state2 to a new value of a join state.
	    * 
	    * @param v The variable for which the values should be joined
	    * @param state1 First SE state.
	    * @param valueInState1 Value in state1.
	    * @param state2 Second SE state.
	    * @param valueInState2 Value in state2.
	    * @param services The services object.
	    * @return A joined value for valueInState1 and valueInState2.
	    */
	   public abstract Pair<HashSet<Term>, Term> joinValuesInStates(
	         LocationVariable v,
	         SymbolicExecutionState state1,
	         Term valueInState1,
	         SymbolicExecutionState state2,
	         Term valueInState2,
	         Services services);
	   
	   /**
	    * Returns the join procedure for the given name.
	    *
	    * @param procName Name of the join procedure.
	    * @return The join procedure of the given name; null if there is no such procedure.
	    */
	   public static JoinProcedure getProcedureByName(String procName) {
	       for (JoinProcedure proc : CONCRETE_RULES) {
	           if (proc != null && proc.toString().equals(procName)) {
	               return proc;
	           }
	       }
	       
	       return null;
	   }
	
}

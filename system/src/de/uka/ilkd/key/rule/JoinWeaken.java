package de.uka.ilkd.key.rule;

import java.util.HashSet;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.util.Pair;

/**
 * Rule that joins two sequents based on weakening.
 * 
 * @author Dominic Scheurer
 */
public class JoinWeaken extends JoinRule {
   
   public static final JoinWeaken INSTANCE = new JoinWeaken();
   private static final Name RULE_NAME = new Name("JoinByWeakening");

   @Override
   protected Pair<Term, Term> joinStates(
         Pair<Term, Term> state1,
         Pair<Term, Term> state2,
         Term programCounter,
         Services services) {
      
      final TermBuilder tb = services.getTermBuilder();
      
      HashSet<LocationVariable> progVars =
            new HashSet<LocationVariable>();
      
      // Collect program variables in Java block
      progVars.addAll(getProgramLocations(programCounter, services));
      // Collect program variables in update
      progVars.addAll(getUpdateLocations(state1.first));
      
      ImmutableList<Term> newElementaryUpdates = ImmutableSLList.nil();
      
      int varNameCounter = (int) System.currentTimeMillis();
      final String varNamePrefix = "v_";
      for (LocationVariable v : progVars) {
         String newName = varNamePrefix + (varNameCounter++);
         
         newElementaryUpdates = newElementaryUpdates.prepend(
               tb.elementary(
                     v,
                     tb.var(
                           new LogicVariable(new Name(newName), v.sort()))));
      }
      
      // Construct weakened symbolic state
      Term newSymbolicState = tb.parallel(newElementaryUpdates);
      
      // Construct path condition as disjunction
      Term newPathCondition = tb.or(state1.second, state2.second);
      
      return new Pair<Term, Term>(newSymbolicState, newPathCondition);
   }

   @Override
   public Name name() {
      return RULE_NAME;
   }

   @Override
   public String displayName() {
      return RULE_NAME.toString();
   }
}

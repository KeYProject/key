package de.uka.ilkd.key.rule;

import java.util.HashSet;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.ElementaryUpdate;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.UpdateJunctor;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.ApplyStrategy.ApplyStrategyInfo;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.symbolic_execution.util.SideProofUtil;
import de.uka.ilkd.key.util.Pair;

/**
 * Rule that joins two sequents based on the if-then-else
 * construction: If two locations are assigned different
 * values in the states, the value in the joined state is
 * chosen based on the path condition. This rule retains
 * total precision.
 * 
 * @author Dominic Scheurer
 */
public class JoinIfThenElse extends JoinRule {
   
   public static final JoinIfThenElse INSTANCE = new JoinIfThenElse();
   private static final Name RULE_NAME = new Name("JoinByIfThenElse");

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
      
      for (LocationVariable v : progVars) {
         // Check if location v is set to different value in both states.
         try {
            Term predicateTerm = tb.func(new Function(new Name("P"), Sort.FORMULA, v.sort()), tb.var(v));
            Term appl1 = tb.apply(state1.first, predicateTerm);
            Term appl2 = tb.apply(state2.first, predicateTerm);
            Term toProve = tb.and(
                  tb.imp(appl1, appl2),
                  tb.imp(appl2, appl1));
            
            ApplyStrategyInfo proofResult = SideProofUtil.startSideProof(
                  services.getProof(),                                  // Parent proof
                  Sequent.createSequent(                                // Sequent to proof
                        Semisequent.EMPTY_SEMISEQUENT,
                        new Semisequent(new SequentFormula(toProve))), 
                  false);                                               // useSimplifyTermProfile
            
            Term rightSide1 = getUpdateRightSideFor(state1.first, v);
            Term rightSide2 = getUpdateRightSideFor(state2.first, v);
            
            boolean proofClosed = proofResult.getProof().closed();
            
            if (proofClosed && rightSide1 != null) {
               //TODO: No if-then-else, same value
               
               newElementaryUpdates = newElementaryUpdates.prepend(
                  tb.elementary(
                        v,
                        rightSide1));
              
            } else if (!proofClosed) {
               //TODO: Apply if-then-else construction, different values
               
               newElementaryUpdates = newElementaryUpdates.prepend(
                     tb.elementary(
                           v,
                           tb.ife(state1.second, rightSide1, rightSide2)));
            }
         }
         catch (ProofInputException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
         }
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
   
   /**
    * Returns the right side for a given location variable in an update
    * (in normal form).
    * 
    * @param update Update term to search.
    * @param leftSide Left side to find the right side for.
    * @return The right side in the update for the given left side.
    */
   private Term getUpdateRightSideFor(Term update, LocationVariable leftSide) {
      if (update.op() instanceof ElementaryUpdate &&
          ((ElementaryUpdate) update.op()).lhs().equals(leftSide)) {
         
         return update.sub(0);
         
      } else if (
            update.op() instanceof UpdateJunctor &&
            update.op().equals(UpdateJunctor.PARALLEL_UPDATE)) {
         
         for (Term sub : update.subs()) {
            Term rightSide = getUpdateRightSideFor(sub, leftSide);
            if (rightSide != null) {
               return rightSide;
            }
         }
         
         return null;
         
      } else {      
         return null;
      }
   }
}

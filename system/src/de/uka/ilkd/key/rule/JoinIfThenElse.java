// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

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
   private static final String DISPLAY_NAME = "JoinByIfThenElse";
   private static final Name RULE_NAME = new Name(DISPLAY_NAME);

   @Override
   protected Pair<Term, Term> joinStates(
         ImmutableList<Pair<Term, Term>> states,
         Term programCounter,
         Services services) {
      
      final TermBuilder tb = services.getTermBuilder();
      
      Pair<Term, Term> joinedState = states.head();
      states = states.tail();
      
      for (Pair<Term,Term> state : states) {
         
         HashSet<LocationVariable> progVars =
               new HashSet<LocationVariable>();
         
         // Collect program variables in Java block
         progVars.addAll(getProgramLocations(programCounter, services));
         // Collect program variables in update
         progVars.addAll(getUpdateLocations(joinedState.first));
         progVars.addAll(getUpdateLocations(state.first));
         
         ImmutableList<Term> newElementaryUpdates = ImmutableSLList.nil();
         
         for (LocationVariable v : progVars) {
            
            Term rightSide1 = getUpdateRightSideFor(joinedState.first, v);
            Term rightSide2 = getUpdateRightSideFor(state.first, v);
            
            if (rightSide1 == null) {
               rightSide1 = tb.var(v);
            }
            
            if (rightSide2 == null) {
               rightSide2 = tb.var(v);
            }
            
            // Check if location v is set to different value in both states.
            try {
               Term predicateTerm = tb.func(new Function(new Name("P"), Sort.FORMULA, v.sort()), tb.var(v));
               Term appl1 = tb.apply(joinedState.first, predicateTerm);
               Term appl2 = tb.apply(state.first, predicateTerm);
               Term toProve = tb.and(
                     tb.imp(appl1, appl2),
                     tb.imp(appl2, appl1));
               
               ApplyStrategyInfo proofResult = SideProofUtil.startSideProof(
                     services.getProof(),                                  // Parent proof
                     Sequent.createSequent(                                // Sequent to proof
                           Semisequent.EMPTY_SEMISEQUENT,
                           new Semisequent(new SequentFormula(toProve))), 
                     false);                                               // useSimplifyTermProfile
               
               boolean proofClosed = proofResult.getProof().closed();
               
               if (proofClosed) {
                  
                  // Arbitrary choice: Take value of first state
                  newElementaryUpdates = newElementaryUpdates.prepend(
                        tb.elementary(
                              v,
                              rightSide1));
                  
               } else {
                  
                  // Apply if-then-else construction: Different values
                  newElementaryUpdates = newElementaryUpdates.prepend(
                        tb.elementary(
                              v,
                              tb.ife(joinedState.second, rightSide1, rightSide2)));
                  
               }
            }
            catch (ProofInputException e) {
               // If proof fails for some reason, just apply
               // if-then-else construction. We still got absolute
               // precision and soundness, only a more complicated
               // resulting sequence.
               
               newElementaryUpdates = newElementaryUpdates.prepend(
                     tb.elementary(
                           v,
                           tb.ife(joinedState.second, rightSide1, rightSide2)));
            }
         }
         
         // Construct weakened symbolic state
         Term newSymbolicState = tb.parallel(newElementaryUpdates);
         
         // Construct path condition as disjunction
         Term newPathCondition = tb.or(joinedState.second, state.second);
         
         joinedState = new Pair<Term, Term>(newSymbolicState, newPathCondition);
      }
      
      return joinedState;
   }

   @Override
   public Name name() {
      return RULE_NAME;
   }

   @Override
   public String displayName() {
      return DISPLAY_NAME;
   }
   
   @Override
   public String toString() {
      return DISPLAY_NAME;
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

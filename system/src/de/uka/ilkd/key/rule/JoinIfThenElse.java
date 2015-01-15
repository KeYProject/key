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
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.sort.Sort;
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
   private static final int MAX_UPDATE_TERM_DEPTH_FOR_CHECKING = 8;

   @Override
   protected Pair<Term, Term> joinStates(
         Pair<Term, Term> state1,
         Pair<Term, Term> state2,
         Term programCounter,
         Services services) {
      
      final TermBuilder tb = services.getTermBuilder();
      
      // Construct path condition as (optimized) disjunction
      Term newPathCondition =
            createSimplifiedDisjunctivePathCondition(state1.second, state2.second, services);
               
      HashSet<LocationVariable> progVars =
            new HashSet<LocationVariable>();
      
      // Collect program variables in Java block
      progVars.addAll(getProgramLocations(programCounter, services));
      // Collect program variables in update
      progVars.addAll(getUpdateLocations(state1.first));
      progVars.addAll(getUpdateLocations(state2.first));
      
      ImmutableList<Term> newElementaryUpdates = ImmutableSLList.nil();
      
      for (LocationVariable v : progVars) {
         
         Term rightSide1 = getUpdateRightSideFor(state1.first, v);
         Term rightSide2 = getUpdateRightSideFor(state2.first, v);
         
         if (rightSide1 == null) {
            rightSide1 = tb.var(v);
         }
         
         if (rightSide2 == null) {
            rightSide2 = tb.var(v);
         }
         
         // Check if location v is set to different value in both states.
         
         // Easy check: Term equality
         boolean proofClosed = rightSide1.equalsModRenaming(rightSide2);
         
         // We skip the check for equal valuation of this variable if
         // the depth threshold is exceeded by one of the right sides.
         // Experiments show a very big time overhead from a depth of
         // about 8-10 on, or sometimes even earlier.
         if (rightSide1.depth() <= MAX_UPDATE_TERM_DEPTH_FOR_CHECKING &&
             rightSide2.depth() <= MAX_UPDATE_TERM_DEPTH_FOR_CHECKING &&
             !proofClosed) {
            
            Term predicateTerm = tb.func(new Function(new Name("P"), Sort.FORMULA, v.sort()), tb.var(v));
            Term appl1 = tb.apply(state1.first, predicateTerm);
            Term appl2 = tb.apply(state2.first, predicateTerm);
            Term toProve = tb.and(
                  tb.imp(appl1, appl2),
                  tb.imp(appl2, appl1));
            
            proofClosed = isProvableWithSplitting(toProve, services);
            
         }
         
         if (proofClosed) {
            
            // Arbitrary choice: Take value of first state
            newElementaryUpdates = newElementaryUpdates.prepend(
                  tb.elementary(
                        v,
                        rightSide1));
            
         } else {
            
            // Apply if-then-else construction: Different values
            
            // We only need the distinguishing subformula; the equal part
            // is not needed. For soundness, it suffices that the "distinguishing"
            // formula is implied by the original path condition; for completeness,
            // we add the common subformula in the new path condition, if it
            // is not already implied by that.
            Pair<Term, Term> distinguishingAndEqualFormula1 =
                  getDistinguishingFormula(state1.second, state2.second, services);
            Term distinguishingFormula = distinguishingAndEqualFormula1.first;
            Term equalSubFormula = distinguishingAndEqualFormula1.second;
            
            Pair<Term, Term> distinguishingAndEqualFormula2 =
                  getDistinguishingFormula(state2.second, state1.second, services);
            Term distinguishingFormula2 = distinguishingAndEqualFormula2.first;
            
            // Choose the shorter distinguishing formula
            boolean commuteSides = false;
            if (countAtoms(distinguishingFormula2) < countAtoms(distinguishingFormula)) {
               distinguishingFormula = distinguishingFormula2;
               commuteSides = true;
            }
            
            // Try an automatic simplification
            distinguishingFormula = trySimplify(services.getProof(), distinguishingFormula);
            
            // Add common subformula to path condition, if necessary
            Term commonPartAlreadyImpliedForm =
                  tb.imp(newPathCondition, equalSubFormula);
            if (!isProvableWithSplitting(commonPartAlreadyImpliedForm, services)) {
               newPathCondition = tb.and(newPathCondition, equalSubFormula);
            }
            
            // Construct the update for the symbolic state
            newElementaryUpdates = newElementaryUpdates.prepend(
                  tb.elementary(
                        v,
                        tb.ife(distinguishingFormula,
                              commuteSides ? rightSide2 : rightSide1,
                                    commuteSides ? rightSide1 : rightSide2)));
            
         }
      }
      
      // Construct weakened symbolic state
      Term newSymbolicState = tb.parallel(newElementaryUpdates);
      
      return new Pair<Term, Term>(newSymbolicState, newPathCondition);
      
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
}

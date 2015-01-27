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
import de.uka.ilkd.key.util.joinrule.SymbolicExecutionState;

/**
 * Rule that joins two sequents based on "total" weakening:
 * Replacement of symbolic state by an update setting every
 * program variable to a fresh Skolem constant, if the
 * respective program variable does not evaluate to the same
 * value in both states - in this case, the original value
 * is preserved (-> idempotency).
 * 
 * @author Dominic Scheurer
 */
public class JoinWeaken extends JoinRule {
   
   public static final JoinWeaken INSTANCE = new JoinWeaken();
   private static final String DISPLAY_NAME = "JoinByWeakening";
   private static final Name RULE_NAME = new Name(DISPLAY_NAME);

   @SuppressWarnings("unused")
   @Override
   protected SymbolicExecutionState joinStates(
         SymbolicExecutionState state1,
         SymbolicExecutionState state2,
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
      
      final String varNamePrefix = "c";
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
         if (rightSide1.depth() <= JoinIfThenElse.MAX_UPDATE_TERM_DEPTH_FOR_CHECKING &&
             rightSide2.depth() <= JoinIfThenElse.MAX_UPDATE_TERM_DEPTH_FOR_CHECKING &&
             !proofClosed &&
             !JoinRule.RIGHT_SIDE_EQUIVALENCE_ONLY_SYNTACTICAL) {
            
            //TODO: The following code appears in several join rules.
            //      Could be extracted to avoid redundancy.

            // Create the predicate term
            final Name predicateSymbName = new Name(tb.newName("P"));
            final Function predicateSymb =
                  new Function(predicateSymbName, Sort.FORMULA, v.sort());
            services.getNamespaces().functions().add(predicateSymb);
            final Term predicateTerm = tb.func(predicateSymb, tb.var(v));

            // Create the formula to check
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
            
            // Apply weakening to fresh constant: Different values
            final Function skolemConstant =
                  getNewScolemConstantForPrefix(varNamePrefix, v.sort(), services);
            
            newElementaryUpdates = newElementaryUpdates.prepend(
                  tb.elementary(
                        v, tb.func(skolemConstant)));
            
         }
         
      }
      
      // Construct weakened symbolic state
      Term newSymbolicState = tb.parallel(newElementaryUpdates);
      
      // Construct path condition as disjunction
      Term newPathCondition =
                  createSimplifiedDisjunctivePathCondition(state1.second, state2.second, services);
      
      return new SymbolicExecutionState(newSymbolicState, newPathCondition);
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

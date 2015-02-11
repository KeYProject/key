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

package de.uka.ilkd.key.rule.join;

import java.util.HashSet;
import java.util.LinkedList;

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
import de.uka.ilkd.key.util.Quadruple;
import de.uka.ilkd.key.util.joinrule.SymbolicExecutionState;

/**
 * Rule that joins two sequents based on the if-then-else
 * construction: If two locations are assigned different
 * values in the states, the value in the joined state is
 * chosen based on the path condition. This rule retains
 * total precision. In contrast to the {@link JoinIfThenElse}
 * rule, the distinction is not realized in the update /
 * symbolic state, but in the antecedent / path condition.
 * This can be much more efficient.
 * 
 * @author Dominic Scheurer
 * @see JoinIfThenElse
 * @see JoinRule
 */
public class JoinIfThenElseAntecedent extends JoinRule {
   
   public static final JoinIfThenElseAntecedent INSTANCE = new JoinIfThenElseAntecedent();
   
   private static final String DISPLAY_NAME = "JoinByIfThenElseAntecedent";
   private static final Name RULE_NAME = new Name(DISPLAY_NAME);
   private static final int MAX_UPDATE_TERM_DEPTH_FOR_CHECKING = 8;

   @SuppressWarnings("unused")
   @Override
   protected SymbolicExecutionState joinStates(
         SymbolicExecutionState state1,
         SymbolicExecutionState state2,
         Term programCounter,
         Services services) {
      
      final TermBuilder tb = services.getTermBuilder();
      
      // Construct path condition as (optimized) disjunction
      Term newPathCondition =
            createSimplifiedDisjunctivePathCondition(state1.second, state2.second, services);
               
      HashSet<LocationVariable> progVars =
            new HashSet<LocationVariable>();
      
      // Collect program variables in Java block
      progVars.addAll(getLocationVariables(programCounter));
      // Collect program variables in update
      progVars.addAll(getUpdateLeftSideLocations(state1.first));
      progVars.addAll(getUpdateLeftSideLocations(state2.first));
      
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
             !proofClosed &&
             !JoinRule.RIGHT_SIDE_EQUIVALENCE_ONLY_SYNTACTICAL) {
            
            //TODO: The following code appears in several join rules.
            //      Could be extracted to avoid redundancy.
            
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
            
            Sort heapSort = (Sort) services.getNamespaces().sorts().lookup("Heap");
            
            if (v.sort().equals(heapSort)) {
               
               Pair<Term, LinkedList<Term>> joinedHeaps = joinHeaps(rightSide1, rightSide2, state1, state2, services);
               newElementaryUpdates = newElementaryUpdates.prepend(tb.elementary(v, joinedHeaps.first));
               newPathCondition = tb.and(newPathCondition, tb.and(joinedHeaps.second));
               
            } else {
               
               newPathCondition = tb.and(newPathCondition,
                     tb.and(getIfThenElseConstraints(
                           tb.var(v),
                           rightSide1,
                           rightSide2,
                           state1,
                           state2,
                           services
                     )));
               
            }
            
         }
      }
      
      // Construct weakened symbolic state
      Term newSymbolicState = tb.parallel(newElementaryUpdates);
      
      return new SymbolicExecutionState(newSymbolicState, newPathCondition);
      
   }
   
   /**
    * Returns a list of if-then-else constraints for the given constrained
    * term, states and if/else terms.
    * 
    * @param constrained The constrained term.
    * @param ifTerm The value for the if case.
    * @param elseTerm The value for the else case.
    * @param state1 First SE state ("if").
    * @param state2 Second SE state ("else").
    * @param services The services object.
    * @return A list of if-then-else constraints for the given constrained
    *    term, states and if/else terms.
    */
   private static LinkedList<Term> getIfThenElseConstraints(
         Term constrained,
         Term ifTerm,
         Term elseTerm,
         SymbolicExecutionState state1,
         SymbolicExecutionState state2,
         Services services) {
      
      TermBuilder tb = services.getTermBuilder();
      LinkedList<Term> result = new LinkedList<Term>();
      
      Quadruple<Term, Term, Term, Boolean> distFormAndRightSidesForITEUpd =
            JoinIfThenElse.createDistFormAndRightSidesForITEUpd(state1, state2, ifTerm, elseTerm, services);
      
      Term cond         = distFormAndRightSidesForITEUpd.first;
      Term ifForm       = distFormAndRightSidesForITEUpd.second;
      Term elseForm     = distFormAndRightSidesForITEUpd.third;
      boolean isSwapped = distFormAndRightSidesForITEUpd.fourth;
      
      Term varEqualsIfForm   = tb.equals(constrained, ifForm);
      Term varEqualsElseForm = tb.equals(constrained, elseForm);
      
      if (!(ifTerm.equals(constrained) && !isSwapped ||
            elseTerm.equals(constrained) && isSwapped)) {
         result.add(tb.imp(cond, varEqualsIfForm));
      }
      
      if (!(elseTerm.equals(constrained) && !isSwapped ||
            ifTerm.equals(constrained) && isSwapped)) {
         result.add(tb.or (cond, varEqualsElseForm));
      }
      
      return result;
      
   }
   
   /**
    * Joins two heaps by if-then-else construction. Tries to shift
    * the if-then-else as deeply into the heap as possible.
    * 
    * @param heap1 The first heap term.
    * @param heap2 The second heap term.
    * @param state1 SE state for the first heap term.
    * @param state2 SE state for the second heap term
    * @param services The services object.
    * @return A joined heap term.
    */
   private Pair<Term, LinkedList<Term>> joinHeaps(
         Term heap1,
         Term heap2,
         SymbolicExecutionState state1,
         SymbolicExecutionState state2,
         Services services) {
      
      //TODO: Parts of this code appear redundantly in different join rules;
      //      it could be sensible to extract those into an own method.
      
      TermBuilder tb = services.getTermBuilder();      
      LinkedList<Term> newConstraints = new LinkedList<Term>();
      
      if (heap1.equals(heap2)) {
         // Keep equal heaps
         return new Pair<Term, LinkedList<Term>>(heap1, newConstraints);
      }
      
      if (!(heap1.op() instanceof Function) ||
            !(heap2.op() instanceof Function)) {
         // Covers the case of two different symbolic heaps
         return new Pair<Term, LinkedList<Term>>(
               JoinIfThenElse.createIfThenElseTerm(state1, state2, heap1, heap2, services),
               newConstraints);
      }
      
      Function storeFunc = (Function) services.getNamespaces().functions().lookup("store");
      Function createFunc = (Function) services.getNamespaces().functions().lookup("create");
      //Note: Check if there are other functions that should be covered.
      //      Unknown functions are treated by if-then-else procedure.
      
      if (((Function) heap1.op()).equals(storeFunc) &&
            ((Function) heap2.op()).equals(storeFunc)) {
         
         // Store operations.
         
         // Decompose the heap operations.
         Term subHeap1 = heap1.sub(0);
         LocationVariable pointer1 = (LocationVariable) heap1.sub(1).op();
         Function field1 = (Function) heap1.sub(2).op();
         Term value1 = heap1.sub(3);
         
         Term subHeap2 = heap2.sub(0);
         LocationVariable pointer2 = (LocationVariable) heap2.sub(1).op();
         Function field2 = (Function) heap2.sub(2).op();
         Term value2 = heap2.sub(3);
         
         if (pointer1.equals(pointer2) && field1.equals(field2)) {
            // Potential for deep merge: Access of same object / field.
            
            Pair<Term, LinkedList<Term>> joinedSubHeap = joinHeaps(subHeap1, subHeap2, state1, state2, services);
            newConstraints.addAll(joinedSubHeap.second);
            
            Term joinedVal = null;
            
            if (value1.equals(value2)) {
               // Idempotency...
               joinedVal = value1;
               
            } else {
               
               // if-then-else
               Function skolemConstant = getNewScolemConstantForPrefix(
                     field1.name().toString(),
                     ((Function) value1.op()).sort(),
                     services);
               
               joinedVal = tb.func(skolemConstant);
               newConstraints.addAll(getIfThenElseConstraints(
                     joinedVal,
                     value1,
                     value2,
                     state1,
                     state2,
                     services));
               
            }
            
            return new Pair<Term, LinkedList<Term>>(
                  tb.func((Function) heap1.op(), joinedSubHeap.first, tb.var(pointer1), tb.func(field1), joinedVal),
                  newConstraints);
         }
         
      } else if (((Function) heap1.op()).equals(createFunc) &&
            ((Function) heap2.op()).equals(createFunc)) {
         
         // Create operations.
         
         // Decompose the heap operations.
         Term subHeap1 = heap1.sub(0);
         LocationVariable pointer1 = (LocationVariable) heap1.sub(1).op();
         
         Term subHeap2 = heap2.sub(0);
         LocationVariable pointer2 = (LocationVariable) heap2.sub(1).op();
         
         if (pointer1.equals(pointer2)) {
            // Same objects are created: Join.
            
            Pair<Term, LinkedList<Term>> joinedSubHeap =
                  joinHeaps(subHeap1, subHeap2, state1, state2, services);
            newConstraints.addAll(joinedSubHeap.second);
            
            return new Pair<Term, LinkedList<Term>>(
                  tb.func((Function) heap1.op(), joinedSubHeap.first, tb.var(pointer1)),
                  newConstraints);
         }
         
         // "else" case is fallback at end of method:
         // if-then-else of heaps.
         
      }

      return new Pair<Term, LinkedList<Term>>(
            JoinIfThenElse.createIfThenElseTerm(state1, state2, heap1, heap2, services),
            newConstraints);
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

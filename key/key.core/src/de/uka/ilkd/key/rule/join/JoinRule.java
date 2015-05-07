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

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

//import de.uka.ilkd.key.gui.joinrule.JoinPartnerSelectionDialog;
import de.uka.ilkd.key.java.JavaProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.rule.RuleAbortException;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.util.Pair;
import de.uka.ilkd.key.util.Triple;
import de.uka.ilkd.key.util.joinrule.JoinRuleUtils;
import de.uka.ilkd.key.util.joinrule.SymbolicExecutionState;
import de.uka.ilkd.key.util.joinrule.SymbolicExecutionStateWithProgCnt;

/**
 * Base for implementing join rules. Extend this class,
 * implement method joinValuesInStates(...) and register in
 * class JavaProfile.<p>
 * 
 * The rule is applicable if the chosen subterm has the
 * form { x := v || ... } PHI and there are potential join
 * candidates.
 * 
 * @author Dominic Scheurer
 * 
 * @see JoinRuleUtils
 * @see JoinWeaken
 * @see JoinIfThenElse
 * @see JoinIfThenElseAntecedent
 * @see JoinWithLatticeAbstraction
 * @see JoinWithSignLattice
 */
public abstract class JoinRule extends JoinRuleUtils implements BuiltInRule {

   /**
    * If set to true, join rules are expected to check the equivalence
    * for right sides (for preserving idempotency) only on a pure syntactical
    * basis. If set to false, they are allowed to do a proof to check the
    * equivalence in the respective contexts.
    */
   protected static final boolean RIGHT_SIDE_EQUIVALENCE_ONLY_SYNTACTICAL = true;
   
   /**
    * Thresholds the maximum depth of right sides in updates for
    * which an equivalence proof is started.
    * 
    * We skip the check for equal valuation of this variable if
    * the depth threshold is exceeded by one of the right sides.
    * Experiments show a very big time overhead from a depth of
    * about 8-10 on, or sometimes even earlier.
    */
   private static final int MAX_UPDATE_TERM_DEPTH_FOR_CHECKING = 8;
   
   @Override
   public final ImmutableList<Goal> apply(Goal goal, final Services services,
         RuleApp ruleApp) throws RuleAbortException {
       
       //TODO: Remove source code related to signaling progress to UI
       //      (has been commented out) if there is no alternative to
       //      using the (now no longer accessible) mediator.
      
//      boolean stoppedInterface = false;
//      if (!mediator().isInAutoMode()) {
//         mediator().stopInterface(true);
//         stoppedInterface = true;
//      }
      
      final TermBuilder tb = services.getTermBuilder();
      final PosInOccurrence pio = ruleApp.posInOccurrence();
      
      if (findPotentialJoinPartners(goal, pio) == null) {
         return null;
      }
      
      ImmutableList<Goal> newGoals = goal.split(1);
      
      final Goal newGoal = newGoals.head();
      
      // Find join partner
//      ImmutableList<Pair<Goal, PosInOccurrence>> joinPartners = findJoinPartners(newGoal, pio);
      ImmutableList<Pair<Goal, PosInOccurrence>> joinPartners = ((JoinRuleBuiltInRuleApp) ruleApp).getJoinPartners();
      
      // Signal this task to UI
//      mediator().getUI().taskStarted(
//            "Joining " + (joinPartners.size() + 1) + " goals",
//            joinPartners.size());
      //TODO: Progress information is so far not properly displayed in the
      //      UI. Obviously, the progress bar does only receive the updates
      //      *after* the task terminated, since the EDT is blocked.
      //      See MainStatusLine#setProgress(final int value).
//      long startTime = System.currentTimeMillis();
      
      // Convert sequents to SE states
      ImmutableList<SymbolicExecutionState> joinPartnerStates = ImmutableSLList.nil();      
      for (Pair<Goal, PosInOccurrence> joinPartner : joinPartners) {
         Triple<Term, Term, Term> partnerSEState =
               sequentToSETriple(joinPartner.first, joinPartner.second, services);
         
         joinPartnerStates = joinPartnerStates.prepend(
               new SymbolicExecutionState(partnerSEState.first, partnerSEState.second, joinPartner.first.node()));
      }
      
      SymbolicExecutionStateWithProgCnt thisSEState =
            sequentToSETriple(newGoal, pio, services);
      
      // The join loop
      SymbolicExecutionState joinedState =
            new SymbolicExecutionState(thisSEState.first, thisSEState.second, goal.node());    

      int progress = 0;
      for (SymbolicExecutionState state : joinPartnerStates) {
         System.out.print("Joining state ");
         System.out.print(progress + 1);
         System.out.print(" of ");
         System.out.println(joinPartners.size());
         
         joinedState = joinStates(joinedState, state, thisSEState.third, services);
         joinedState.setCorrespondingNode(goal.node());
         
         // Signal progress to UI
//         mediator().getUI().taskProgress(++progress);
      }
      
      Term resultPathCondition = joinedState.second;
      resultPathCondition = trySimplify(services.getProof(), resultPathCondition, true);
      
      // Delete previous sequents      
      clearSemisequent(newGoal, true);
      clearSemisequent(newGoal, false);
      
      // Add new antecedent (path condition)
      for (Term antecedentFormula : getConjunctiveElementsFor(resultPathCondition)) {
         SequentFormula newAntecedent = new SequentFormula(antecedentFormula);
         newGoal.addFormula(newAntecedent, true, false);
      }
      
      // Add new succedent (symbolic state & program counter)
      Term succedentFormula = tb.apply(joinedState.first, thisSEState.third);
      SequentFormula newSuccedent = new SequentFormula(succedentFormula);
      newGoal.addFormula(
            new SequentFormula(succedentFormula),
            new PosInOccurrence(newSuccedent, PosInTerm.getTopLevel(), false));
      
      // Close partner goals
      for (Pair<Goal, PosInOccurrence> joinPartner : joinPartners) {
         closeJoinPartnerGoal(
               newGoal.node(),
               joinPartner.first,
               joinedState,
               sequentToSEPair(joinPartner.first, joinPartner.second, services),
               thisSEState.third);
      }

//      long endTime = System.currentTimeMillis();
//      long duration = endTime - startTime;
//      mediator().getUI().taskFinished(new DefaultTaskFinishedInfo(
//            this,                          // source
//            joinedState,                   // result
//            mediator().getSelectedProof(), // proof
//            duration,                      // time
//            1 + joinPartners.size(),       // applied rules
//            0));                           // closed goals
//      
//      if (stoppedInterface) {
//         mediator().startInterface(true);
//      }
      
      return newGoals;
   }
   
   /**
    * Joins two SE states (U1,C1,p) and (U2,C2,p) according to the method
    * {@link JoinRule#joinValuesInStates(LocationVariable, SymbolicExecutionState, Term, SymbolicExecutionState, Term, Services)}.
    * p must be the same in both states, so it is supplied separately.<p>
    * 
    * Override this method for special join procedures.
    * 
    * @param state1 First state to join.
    * @param state2 Second state to join.
    * @param programCounter The formula \&lt;{ ... }\&gt; phi
    *   consisting of the common program counter and the post condition.
    * @param services The services object.
    * @return A new joined SE state (U*,C*) which is a weakening
    *    of the original states.
    */
   @SuppressWarnings("unused")
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
      progVars.addAll(getLocationVariables(programCounter, services));
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
            
            Term predicateTerm = tb.func(new Function(new Name("P"), Sort.FORMULA, v.sort()), tb.var(v));
            Term appl1 = tb.apply(state1.first, predicateTerm);
            Term appl2 = tb.apply(state2.first, predicateTerm);
            Term toProve = tb.and(
                  tb.imp(appl1, appl2),
                  tb.imp(appl2, appl1));
            
            proofClosed = isProvableWithSplitting(toProve, services);
            
         }
         
         if (proofClosed) {
            
            // Arbitrary choice: Take value of first state if
            // this does not equal the program variable itself
            if (!rightSide1.equals(tb.var(v))) {
               newElementaryUpdates = newElementaryUpdates.prepend(
                     tb.elementary(
                           v,
                           rightSide1));
            }
            
         } else {
            
            // Apply if-then-else construction: Different values
            
            Sort heapSort = (Sort) services.getNamespaces().sorts().lookup("Heap");
            
            if (v.sort().equals(heapSort)) {
               
               Pair<HashSet<Term>, Term> joinedHeaps = joinHeaps(v, rightSide1, rightSide2, state1, state2, services);
               newElementaryUpdates = newElementaryUpdates.prepend(tb.elementary(v, joinedHeaps.second));
               newPathCondition = tb.and(newPathCondition, tb.and(joinedHeaps.first));
               
            } else {
               
               Pair<HashSet<Term>, Term> joinedVal =
                     joinValuesInStates(v, state1, rightSide1, state2, rightSide2, services);
               
               newElementaryUpdates = newElementaryUpdates.prepend(
                     tb.elementary(
                           v,
                           joinedVal.second));
               
               newPathCondition = tb.and(
                     newPathCondition,
                     tb.and(joinedVal.first));
               
            } // end else of if (v.sort().equals(heapSort))
            
         } // end else of if (proofClosed)
         
      } // end for (LocationVariable v : progVars)
      
      // Construct weakened symbolic state
      Term newSymbolicState = tb.parallel(newElementaryUpdates);
      
      return new SymbolicExecutionState(newSymbolicState, newPathCondition);
      
   }
   
   /**
    * Joins two heaps in a zip-like procedure. The fallback
    * is an if-then-else construct that is tried to be shifted
    * as far inwards as possible.<p>
    * 
    * Override this method for specialized heap join procedures.
    * 
    * @param heapVar The heap variable for which the
    *    values should be joined.
    * @param heap1 The first heap term.
    * @param heap2 The second heap term.
    * @param state1 SE state for the first heap term.
    * @param state2 SE state for the second heap term
    * @param services The services object.
    * @return A joined heap term.
    */
   protected Pair<HashSet<Term>, Term> joinHeaps(
         LocationVariable heapVar,
         Term heap1,
         Term heap2,
         SymbolicExecutionState state1,
         SymbolicExecutionState state2,
         Services services) {
      
      TermBuilder tb = services.getTermBuilder();      
      HashSet<Term> newConstraints = new HashSet<Term>();
      
      if (heap1.equals(heap2)) {
         // Keep equal heaps
         return new Pair<HashSet<Term>, Term>(newConstraints, heap1);
      }
      
      if (!(heap1.op() instanceof Function) ||
            !(heap2.op() instanceof Function)) {
         // Covers the case of two different symbolic heaps
         return new Pair<HashSet<Term>, Term>(
               newConstraints,
               JoinIfThenElse.createIfThenElseTerm(state1, state2, heap1, heap2, services));
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
            
            Pair<HashSet<Term>, Term> joinedSubHeap = joinHeaps(heapVar, subHeap1, subHeap2, state1, state2, services);
            newConstraints.addAll(joinedSubHeap.first);
            
            Term joinedVal = null;
            
            if (value1.equals(value2)) {
               // Idempotency...
               joinedVal = value1;
               
            } else {
               
               Pair<HashSet<Term>, Term> joinedValAndConstr =
                     joinValuesInStates(
                           new LocationVariable(
                                 new ProgramElementName(field1.name().toString()),
                                 value1.sort()),
                           state1, value1, state2, value2, services);

               newConstraints.addAll(joinedValAndConstr.first);
               joinedVal = joinedValAndConstr.second;
               
            }
            
            return new Pair<HashSet<Term>, Term>(
                  newConstraints,
                  tb.func((Function) heap1.op(), joinedSubHeap.second, tb.var(pointer1), tb.func(field1), joinedVal));
            
         } // end if (pointer1.equals(pointer2) && field1.equals(field2))
         
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
            
            Pair<HashSet<Term>, Term> joinedSubHeap =
                  joinHeaps(heapVar, subHeap1, subHeap2, state1, state2, services);
            newConstraints.addAll(joinedSubHeap.first);
            
            return new Pair<HashSet<Term>, Term>(
                  newConstraints,
                  tb.func((Function) heap1.op(), joinedSubHeap.second, tb.var(pointer1)));
         }
         
         // "else" case is fallback at end of method:
         // if-then-else of heaps.
         
      } // end else of else if (((Function) heap1.op()).equals(createFunc) && ((Function) heap2.op()).equals(createFunc))

      return new Pair<HashSet<Term>, Term>(
            newConstraints,
            JoinIfThenElse.createIfThenElseTerm(state1, state2, heap1, heap2, services));
      
   }
         
   
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
   protected abstract Pair<HashSet<Term>, Term> joinValuesInStates(
         LocationVariable v,
         SymbolicExecutionState state1,
         Term valueInState1,
         SymbolicExecutionState state2,
         Term valueInState2,
         Services services);

   /**
    * We admit top level formulas of the form \&lt;{ ... }\&gt; phi
    * and U \&lt;{ ... }\&gt; phi, where U must be an update
    * in normal form, i.e. a parallel update of elementary
    * updates.
    * 
    * @param goal Current goal.
    * @param pio Position of selected sequent formula.
    * @return true iff a suitable top level formula for joining.
    */
   @Override
   public boolean isApplicable(Goal goal, PosInOccurrence pio) {
      // Note: If the join rule is applicable for automatic
      //       rule application, the symbolic execution strategy
      //       does not seem to work as usual!
       
       

      return isApplicable(goal, pio,
            true,  // Only allow application of rule for manual calls
            true); // Do the check for partner existence
   }
   
   /**
    * We admit top level formulas of the form \&lt;{ ... }\&gt; phi
    * and U \&lt;{ ... }\&gt; phi, where U must be an update
    * in normal form, i.e. a parallel update of elementary
    * updates. We require that phi does not contain a Java block.
    * When checkAutomatic is set to true, only interactive goals
    * are admitted.
    * 
    * @param goal Current goal.
    * @param pio Position of selected sequent formula.
    * @param checkAutomatic If true, only interactive goals are applicable.
    * @param doJoinPartnerCheck Checks for available join partners iff this flag is set to true.
    * @return true iff a suitable top level formula for joining.
    */
   public boolean isApplicable(
         Goal goal, PosInOccurrence pio, boolean checkAutomatic, boolean doJoinPartnerCheck) {
      // We admit top level formulas of the form \<{ ... }\> phi
      // and U \<{ ... }\> phi, where U must be an update
      // in normal form, i.e. a parallel update of elementary
      // updates.
       
       //TODO: How can we find out whether this rule is applied by an automatic strategy?
       //      Did this using the mediator previously, but no longer possible after
       //      refactoring. The below "solution" only allows merging for interactive
       //      goals if checkAutomatic is true.
      if (checkAutomatic && goal.isAutomatic()) {
          return false;
      }
      
      if (pio != null) {
         
         if (!pio.isTopLevel()) {
            return false;
         }
         
         Term selected = pio.subTerm();
         
         Term termAfterUpdate = selected;
         
         if (selected.op() instanceof UpdateApplication) {
            Term update = selected.sub(0);
            
            if (isUpdateNormalForm(update) && selected.subs().size() > 1) {
               termAfterUpdate = selected.sub(1);
            } else {
               return false;
            }
         }
         
         // Term after update must have the form "phi" or "\<{...}\> phi" or
         // "\[{...}\]", where phi must not contain a Java block.
         if (termAfterUpdate.op() instanceof Modality &&
               !termAfterUpdate.sub(0).javaBlock().equals(JavaBlock.EMPTY_JAVABLOCK)) {
            return false;
         } else if (termAfterUpdate.op() instanceof UpdateApplication) {
            return false;
         }
         
         return !doJoinPartnerCheck || findPotentialJoinPartners(goal, pio).size() > 0;
         
      } else {
         
         return false;
         
      }
   }
   
   @Override
   public boolean isApplicableOnSubTerms() {
       // TODO: Check if this has to be changed. This is a stub!
       return false;
   }
   
   @Override
   public IBuiltInRuleApp createApp(PosInOccurrence pio, TermServices services) {
      return new JoinRuleBuiltInRuleApp(this, pio);
   }
   
   /**
    * Finds all suitable join partners.
    * 
    * @param goal Current goal to join.
    * @param pio Position of update-program counter formula in goal.
    * @param services The services object.
    * @return A list of suitable join partners. May be empty if none exist.
    */
   public ImmutableList<Pair<Goal,PosInOccurrence>> findPotentialJoinPartners(
         Goal goal, PosInOccurrence pio) {
      
      Services services = goal.proof().getServices();
      
      ImmutableList<Goal> allGoals =
            services.getProof().getSubtreeGoals(services.getProof().root());
      
      // Find potential partners -- for which isApplicable is true and
      // they have the same program counter (and post condition).
      ImmutableList<Pair<Goal,PosInOccurrence>> potentialPartners = ImmutableSLList.nil();
      for (Goal g : allGoals) {
         if (!g.equals(goal) && !g.node().isLinked()) {
            Semisequent succedent = g.sequent().succedent();
            for (int i = 0; i < succedent.size(); i++) {
               SequentFormula f = succedent.get(i);
               
               PosInTerm pit = PosInTerm.getTopLevel();
               pit.down(i);

               PosInOccurrence gPio = new PosInOccurrence(f, pit, false);
               if (isApplicable(g, gPio, false, false)) {
                  Triple<Term, Term, Term> ownSEState = sequentToSETriple(
                        goal, pio, services);
                  Triple<Term, Term, Term> partnerSEState = sequentToSETriple(
                        g, gPio, services);

                  //NOTE: The equality check for the Java blocks can be problematic,
                  //  since KeY instantiates declared program variables with different
                  //  identifiers; e.g. {int x = 10; if (x...)} could get {x_1 = 10; if (x_1...)}
                  //  in one and {x_2 = 10; if (x_2...)} in the other branch. This cannot
                  //  be circumvented with equalsModRenaming, since at this point, the
                  //  PVs are already declared. We therefore check equality modulo
                  //  switching to branch-unique (and not globally unique) names.
                  
                  JavaProgramElement ownProgramElem     = ownSEState.third.javaBlock().program();
                  JavaProgramElement partnerProgramElem = partnerSEState.third.javaBlock().program();
                  
                  Term ownPostCond     = ownSEState.third.op() instanceof Modality ? ownSEState.third.sub(0) : ownSEState.third;
                  Term partnerPostCond = partnerSEState.third.op() instanceof Modality ? partnerSEState.third.sub(0) : partnerSEState.third;
                  
                  // Requirement: Same post condition, matching program parts
                  if (ownPostCond.equals(partnerPostCond) &&
                        equalsModBranchUniqueRenaming(
                           ownProgramElem,
                           partnerProgramElem,
                           goal.node(),
                           services)) {
                     
                     potentialPartners = potentialPartners.prepend(
                           new Pair<Goal, PosInOccurrence> (g, gPio));
                     
                  }
               }
            }
         }
      }
      
      return potentialPartners;
   }
}

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

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.core.DefaultTaskFinishedInfo;
import de.uka.ilkd.key.gui.joinrule.JoinPartnerSelectionDialog;
import de.uka.ilkd.key.java.JavaProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.DefaultBuiltInRuleApp;
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
 * implement method joinStates(...) and register in
 * class JavaProfile.<p>
 * 
 * The rule is applicable if the chosen subterm has the
 * form { x := v || ... } \&lt;{ ... }\&gt; PHI and there
 * are potential join candidates. In automatic mode, all
 * candidates are chosen for a merge; in interactive mode
 * (set selected goal to interactive), a GUI dialog pops
 * up and asks for a manual selection.
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
   
   @Override
   public ImmutableList<Goal> apply(Goal goal, final Services services,
         RuleApp ruleApp) throws RuleAbortException {
      
      boolean stoppedInterface = false;
      if (!mediator().isInAutoMode()) {
         mediator().stopInterface(true);
         stoppedInterface = true;
      }
      
      final TermBuilder tb = services.getTermBuilder();
      final PosInOccurrence pio = ruleApp.posInOccurrence();
      
      if (findPotentialJoinPartners(goal, pio) == null) {
         return null;
      }
      
      ImmutableList<Goal> newGoals = goal.split(1);
      
      final Goal newGoal = newGoals.head();
      
      // Find join partner
      ImmutableList<Pair<Goal, PosInOccurrence>> joinPartners = findJoinPartners(newGoal, pio);
      
      // Signal this task to UI
      mediator().getUI().taskStarted(
            "Joining " + (joinPartners.size() + 1) + " goals",
            joinPartners.size());
      //TODO: Progress information is so far not properly displayed in the
      //      UI. Obviously, the progress bar does only receive the updates
      //      *after* the task terminated, since the EDT is blocked.
      //      See MainStatusLine#setProgress(final int value).
      long startTime = System.currentTimeMillis();
      
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
         mediator().getUI().taskProgress(++progress);
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

      long endTime = System.currentTimeMillis();
      long duration = endTime - startTime;
      mediator().getUI().taskFinished(new DefaultTaskFinishedInfo(
            this,                          // source
            joinedState,                   // result
            mediator().getSelectedProof(), // proof
            duration,                      // time
            1 + joinPartners.size(),       // applied rules
            0));                           // closed goals
      
      if (stoppedInterface) {
         mediator().startInterface(true);
      }
      
      return newGoals;
   }
   
   /**
    * Joins two SE states (U1,C1,p) and (U2,C2,p). p must
    * be the same in both states, so it is supplied separately.
    * 
    * @param state1 First state to join.
    * @param state2 Second state to join.
    * @param programCounter The formula \&lt;{ ... }\&gt; phi
    *   consisting of the common program counter and the post condition.
    * @param services The services object.
    * @return A new joined SE state (U*,C*) which is a weakening
    *    of the original states.
    */
   protected abstract SymbolicExecutionState joinStates(
         SymbolicExecutionState state1,
         SymbolicExecutionState state2,
         Term programCounter,
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
      
      // At first, we allow only manual application of this rule,
      // since in early stages of experimenting, it was possible
      // to perform an infinite chain of applications, which was
      // done by the automatic strategy.
      if (checkAutomatic && mediator().isInAutoMode()) {
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
         } else {
            // We do not merge states without updates
            // by weakening. Should also not happen
            // in practice.
            return false;
         }
         
         // Check for form "\<{...}\> phi", where phi must not contain a Java block.
         if (termAfterUpdate.op() instanceof Modality &&
               termAfterUpdate.sub(0).javaBlock().equals(JavaBlock.EMPTY_JAVABLOCK)) {
            return !doJoinPartnerCheck || findPotentialJoinPartners(goal, pio).size() > 0;
         } else {
            return false;
         }
         
      } else {
         
         return false;
         
      }
   }
   
   @Override
   public IBuiltInRuleApp createApp(PosInOccurrence pos, TermServices services) {
      return new DefaultBuiltInRuleApp(this, pos);
   }
   
   /**
    * Finds all suitable join partners.
    * 
    * @param goal Current goal to join.
    * @param pio Position of update-program counter formula in goal.
    * @param services The services object.
    * @return A list of suitable join partners. May be empty if none exist.
    */
   private ImmutableList<Pair<Goal,PosInOccurrence>> findPotentialJoinPartners(
         Goal goal, PosInOccurrence pio/*, Services services*/) {
      
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
                  
                  Term ownPostCond     = ownSEState.third.sub(0);
                  Term partnerPostCond = partnerSEState.third.sub(0);
                  
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
   
   /**
    * Selects among suitable join partners using GUI input.
    * 
    * @param goal Current goal to join.
    * @param pio Position of update-program counter formula in goal.
    * @param services The services object.
    * @return A list of suitable join partners. May be empty if none exist / selected.
    */
   private ImmutableList<Pair<Goal,PosInOccurrence>> findJoinPartners(
         Goal goal, PosInOccurrence pio) {
      
      Services services = goal.proof().getServices();
      
      ImmutableList<Pair<Goal,PosInOccurrence>> potentialPartners =
            findPotentialJoinPartners(goal, pio);
      
      JoinPartnerSelectionDialog selectionDialog =
            new JoinPartnerSelectionDialog(goal, pio, potentialPartners, services);
      selectionDialog.setVisible(true);
      
      return selectionDialog.getChosen();
   }
}

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
import de.uka.ilkd.key.gui.joinrule.JoinPartnerSelectionDialog;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.visitor.CreatingASTVisitor;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.ElementaryUpdate;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.logic.op.UpdateJunctor;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.util.Pair;
import de.uka.ilkd.key.util.Triple;

/**
 * Base for implementing join rules. Extend this class,
 * implement method joinStates(...) and register in
 * class JavaProfile.
 * 
 * The rule is applicable if the chosen subterm has the
 * form { x := v || ... } \&lt;{ ... }\&gt; PHI and there
 * are potential join candidates. In automatic mode, all
 * candidates are chosen for a merge; in interactive mode
 * (set selected goal to interactive), a GUI dialog pops
 * up and asks for a manual selection.
 * 
 * @author Dominic Scheurer
 */
public abstract class JoinRule implements BuiltInRule {

   @Override
   public ImmutableList<Goal> apply(Goal goal, Services services,
         RuleApp ruleApp) throws RuleAbortException {
      
      final TermBuilder tb = services.getTermBuilder();
      final PosInOccurrence pio = ruleApp.posInOccurrence();
      
      if (findPotentialJoinPartners(goal, pio) == null) {
         return null;
      }
      
      ImmutableList<Goal> newGoal = goal.split(1);
      Goal g = newGoal.head();
      
      // Find join partner
      ImmutableList<Pair<Goal, PosInOccurrence>> joinPartners = findJoinPartners(g, pio);
      
      // Convert sequents to SE states
      Triple<Term, Term, Term> thisSEState =
            sequentToSETriple(g, pio, services);
      
      Pair<Term, Term> joinedState =
            new Pair<Term, Term>(thisSEState.first, thisSEState.second);
      
      for (Pair<Goal, PosInOccurrence> joinPartner : joinPartners) {
         Triple<Term, Term, Term> partnerSEState =
               sequentToSETriple(joinPartner.first, joinPartner.second, services);
         
         // Join them!
         joinedState = joinStates(
               new Pair<Term, Term> (joinedState.first, joinedState.second),
               new Pair<Term, Term> (partnerSEState.first, partnerSEState.second),
               thisSEState.third,
               services);
         
         // Close partner goals
         // TODO: The procedure here appends a node "==> true" to the partner
         //       goals and closes them afterward. However, with this technique
         //       it is not possible anymore to use the "undo last step" function,
         //       since only this node can be set back anymore -- it is not
         //       even possible to prune the partner nodes, because they are
         //       closed goals... Can we do something different? Or register
         //       something with the undo function?
         closeJoinPartnerGoal(goal, joinPartner.first, joinedState, thisSEState.third);
      }
      
      // Delete previous sequents      
      clearSemisequent(g, true);
      clearSemisequent(g, false);
      
      // Add new antecedent (path condition)
      SequentFormula newAntecedent = new SequentFormula(joinedState.second);
      g.addFormula(
            newAntecedent,
            new PosInOccurrence(newAntecedent, PosInTerm.getTopLevel(), true));
      
      // Add new succedent (symbolic state & program counter)
      SequentFormula newSuccedent = new SequentFormula(
            tb.apply(joinedState.first, thisSEState.third));
      g.addFormula(
            newSuccedent,
            new PosInOccurrence(newSuccedent, PosInTerm.getTopLevel(), false));
      
      return newGoal;
   }
   
   /**
    * Joins two SE states (U1,C1,p) and (U2,C2,p). p must
    * be the same in both states, so it is supplied separately.
    * 
    * @param state1 First SE state.
    * @param state2 Second SE state.
    * @param services The services object.
    * @return A new joined SE state (U*,C*) which is
    *   a weakening of both the original states.
    */
   protected abstract Pair<Term, Term> joinStates(
         Pair<Term, Term> state1,
         Pair<Term, Term> state2,
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
      
      return isApplicable(goal, pio, false, true);
   }
   
   /**
    * We admit top level formulas of the form \&lt;{ ... }\&gt; phi
    * and U \&lt;{ ... }\&gt; phi, where U must be an update
    * in normal form, i.e. a parallel update of elementary
    * updates. When checkAutomatic is set to true, only interactive
    * goals are admitted.
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
            isUpdateNormalForm(update);
            
            if (selected.subs().size() > 1) {
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
         
         if (termAfterUpdate.op() instanceof Modality) {
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
    * @param u The update (in normal form) to extract program locations from.
    * @return All program locations (left sides) in the given update.
    */
   protected HashSet<LocationVariable> getUpdateLocations(Term u) {
      if (u.op() instanceof ElementaryUpdate) {
         
         HashSet<LocationVariable> result = new HashSet<LocationVariable>();
         result.add((LocationVariable) ((ElementaryUpdate) u.op()).lhs());
         return result;
         
      } else if (u.op() instanceof UpdateJunctor) {
         
         HashSet<LocationVariable> result = new HashSet<LocationVariable>();
         for (Term sub : u.subs()) {
            result.addAll(getUpdateLocations(sub));
         }
         return result;
         
      } else {
         
         throw new IllegalStateException("Update should be in normal form!");
         
      }
   }
   
   /**
    * Returns all used program locations in the given term. The term
    * must be of the form \<{ ... }\> phi (or \[{ ... }\] phi).
    * 
    * @param programCounterTerm The term (program counter) to extract
    *    locations from.
    * @param services The Services object.
    * @return The set of contained program locations.
    */
   protected HashSet<LocationVariable> getProgramLocations(
         Term programCounterTerm, Services services) {
      CollectProgramVariablesVisitor visitor =
            new CollectProgramVariablesVisitor(
               programCounterTerm.javaBlock().program(),
               true,
               services);
      
      HashSet<LocationVariable> progVars =
            new HashSet<LocationVariable>();
      
      // Collect program variables in Java block
      visitor.start();
      progVars.addAll(visitor.getVariables());
      
      return progVars;
   }
   
   /**
    * Closes the given partner goal, adding a label pointing to
    * the serial number of the remaining join node.
    * 
    * @param thisGoal Parent of remaining join node.
    * @param joinPartner Partner goal to close.
    */
   private void closeJoinPartnerGoal(
         Goal thisGoal, Goal joinPartner, Pair<Term, Term> joinState, Term pc) {
      Services services = thisGoal.proof().getServices();
      TermBuilder tb = services.getTermBuilder();
      
      // Splitting the goal leads to an exception (null pointer)
      // in AbstractNonDuplicateAppFeature#sameApplication
      // (line 70); newApp.rule() or ruleCmp.rule() is null for
      // the node if split like here. 
//      ImmutableList<Goal> jpNewGoals = joinPartner.split(1);
//      Goal jpNewGoal = jpNewGoals.head();
//      jpNewGoal.setBranchLabel("Joined with node " + thisGoal.node().serialNr());
      
      Term impForm = tb.imp(joinState.second, tb.apply(joinState.first, pc));
      joinPartner.addFormula(new SequentFormula(impForm), true, true);
   }
   
   /**
    * Deletes all formulae of the succedent / antecedent.
    * 
    * @param goal Goal to delete formulae from.
    * @param antec If true, antecedent formulae are deleted, else
    *    succedent formulae.
    */
   private void clearSemisequent(Goal goal, boolean antec) {
      Semisequent semiseq = antec ?
            goal.sequent().antecedent() :
            goal.sequent().succedent();
      for (int i = 0; i < semiseq.size(); i++) {
         SequentFormula f = semiseq.get(i);
         
         PosInTerm pit = PosInTerm.getTopLevel();
         pit.down(i);
         
         PosInOccurrence gPio = new PosInOccurrence(f, pit, antec);
         goal.removeFormula(gPio);
      }
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
         Goal goal, PosInOccurrence pio/*, Services services*/) {
      
      Services services = goal.proof().getServices();
      
      ImmutableList<Pair<Goal,PosInOccurrence>> potentialPartners =
            findPotentialJoinPartners(goal, pio);
      
      if (goal.isAutomatic()) {
         return potentialPartners;
      } else {
         JoinPartnerSelectionDialog selectionDialog =
               new JoinPartnerSelectionDialog(goal, pio, potentialPartners, services);
         selectionDialog.setVisible(true);
         
         return selectionDialog.getChosen();
      }
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
         if (!g.equals(goal)) {
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
                  
                  if (ownSEState.third.equals(partnerSEState.third)) {
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
    * Converts a sequent (given by goal & pos in occurrence) to
    * an SE state (U,C,p).
    * 
    * @param goal Current goal.
    * @param pio Position of update-program counter formula in goal.
    * @param services The services object.
    * @return An SE state (U,C,p).
    */
   private Triple<Term, Term, Term> sequentToSETriple(
         Goal goal, PosInOccurrence pio, Services services) {
      
      ImmutableList<SequentFormula> pathConditionSet = ImmutableSLList.nil();
      pathConditionSet = pathConditionSet.prepend(goal.sequent().antecedent().toList());
      
      Term selected = pio.subTerm();
      
      for (SequentFormula sf : goal.sequent().succedent()) {
         if (!sf.formula().equals(selected)) {
            pathConditionSet = pathConditionSet.prepend(
                  new SequentFormula(services.getTermBuilder().not(sf.formula())));
         }
      }
      
      return new Triple<Term, Term, Term>(
            selected.sub(0),                               // Update
            joinListToAndTerm(pathConditionSet, services), // Path Condition
            selected.sub(1));                              // Program Counter and Post Condition
   }
   
   /**
    * Joins a list of sequent formulae to an and-connected term.
    * 
    * @param formulae Formulae to join.
    * @param services The services object.
    * @return And-formula connecting the given terms.
    */
   private Term joinListToAndTerm(ImmutableList<SequentFormula> formulae, Services services) {
      if (formulae.size() == 0) {
         return services.getTermBuilder().tt();
      } else if (formulae.size() == 1) {
         return formulae.head().formula();
      } else {
         return services.getTermBuilder().and(
               formulae.head().formula(),
               joinListToAndTerm(formulae.tail(), services));
      }
   }

   /**
    * Checks if an update is of the form { x := v || ... || z := q}.
    * 
    * @param u Update to check.
    * @return true iff u is in normal form.
    */
   private boolean isUpdateNormalForm(Term u) {
      if (u.op() instanceof ElementaryUpdate) {
         return true;
      } else if (u.op() instanceof UpdateJunctor) {
         boolean result = true;
         for (Term sub : u.subs()) {
            result = result && isUpdateNormalForm(sub);
         }
         return result;
      } else {
         return false;
      }
   }
   
   /**
    * Visitor for collecting program locations in a Java block.
    * 
    * @author Dominic Scheurer
    */
   private class CollectProgramVariablesVisitor extends CreatingASTVisitor {
      private HashSet<LocationVariable> variables =
            new HashSet<LocationVariable>();

      public CollectProgramVariablesVisitor(ProgramElement root,
            boolean preservesPos, Services services) {
         super(root, preservesPos, services);
      }
      
      @Override
      public void performActionOnLocationVariable(LocationVariable x) {
         // Calling super leads to an EmptyStackException...
         // Without, it perfectly works.
//         super.performActionOnLocationVariable(x);
         
         variables.add(x);
      }
      
      /**
       * Call start() before calling this method!
       * 
       * @return All program locations in the given Java block.
       */
      public HashSet<LocationVariable> getVariables() {
         return variables;
      }
      
   }
}

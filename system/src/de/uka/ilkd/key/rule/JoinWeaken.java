package de.uka.ilkd.key.rule;

import java.util.HashSet;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.visitor.CreatingASTVisitor;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.ElementaryUpdate;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.logic.op.UpdateJunctor;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.util.Pair;
import de.uka.ilkd.key.util.Triple;

/**
 * Rule that joins two sequents based on weakening.
 * 
 * @author Dominic Scheurer
 */
public class JoinWeaken implements BuiltInRule {
   
   public static final JoinWeaken INSTANCE = new JoinWeaken();

   @Override
   public ImmutableList<Goal> apply(Goal goal, Services services,
         RuleApp ruleApp) throws RuleAbortException {
      
      final TermBuilder tb = services.getTermBuilder();
      final PosInOccurrence pio = ruleApp.posInOccurrence();
      Term selected = pio.subTerm();
      
      if (findJoinPartner(goal, pio, services) == null) {
         return null;
      }
      
      ImmutableList<Goal> newGoal = goal.split(1);
      Goal g = newGoal.head();
      
      Term update = null;
      Term termAfterUpdate = selected;
      
      if (selected.op() instanceof UpdateApplication) {
         update          = selected.sub(0);
         termAfterUpdate = selected.sub(1);
      }
      
      CollectProgramVariablesVisitor visitor =
            new CollectProgramVariablesVisitor(
               termAfterUpdate.javaBlock().program(),
               true,
               services);
      
      HashSet<LocationVariable> progVars =
            new HashSet<LocationVariable>();
      
      // Collect program variables in Java block
      visitor.start();
      progVars.addAll(visitor.getVariables());
      // Collect program variables in update
      progVars.addAll(getUpdateLocations(update));
      
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
      
      // Find join partner
      Pair<Goal,PosInOccurrence> joinPartner = findJoinPartner(g, pio, services);
      
      // Convert sequents to SE states
      Triple<Term, Term, Term> thisSEState =
            sequentToSETriple(g, pio, services);
      Triple<Term, Term, Term> partnerSEState =
            sequentToSETriple(joinPartner.first, joinPartner.second, services);
      
      // Construct weakened update and modality formula
      Term newUpdate  = tb.parallel(newElementaryUpdates);
      Term newFormula = tb.apply(newUpdate, termAfterUpdate);
      
      // Delete previous sequents      
      clearSemisequent(g, true);
      clearSemisequent(g, false);
      
      // Add new antecedent (path condition)
      SequentFormula newAntecedent = new SequentFormula(services.getTermBuilder()
            .or(thisSEState.second, partnerSEState.second));
      g.addFormula(
            newAntecedent,
            new PosInOccurrence(newAntecedent, PosInTerm.getTopLevel(), true));
      
      // Add new succedent (symbolic state & program counter)
      SequentFormula newSuccedent = new SequentFormula(newFormula);
      g.addFormula(
            newSuccedent,
            new PosInOccurrence(newSuccedent, PosInTerm.getTopLevel(), false));
      
      // Close partner goal
      ImmutableList<Goal> jpNewGoals = joinPartner.first.split(1);
      Goal jpNewGoal = jpNewGoals.head();
      jpNewGoal.setBranchLabel("Joined with node " + goal.node().serialNr());
      
      clearSemisequent(jpNewGoal, true);
      clearSemisequent(jpNewGoal, false);
      SequentFormula trueSeqForm = new SequentFormula(services.getTermBuilder().tt());
      jpNewGoal.addFormula(
            trueSeqForm,
            new PosInOccurrence(trueSeqForm, PosInTerm.getTopLevel(), false));
      
      jpNewGoal.proof().closeGoal(joinPartner.first);
      
      return newGoal;
   }

   @Override
   public Name name() {
      return new Name("JoinWeaken");
   }

   @Override
   public String displayName() {
      return "JoinWeaken";
   }

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
      return isApplicable(goal, pio, true);
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
    * @param checkAutomatic if true, only interactive goals are applicable.
    * @return true iff a suitable top level formula for joining.
    */
   public boolean isApplicable(Goal goal, PosInOccurrence pio, boolean checkAutomatic) {
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
            return true;
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
    * Finds a suitable join partner.
    * 
    * @param goal Current goal to join.
    * @param pio Position of update-program counter formula in goal.
    * @param services The services object.
    * @return A suitable join partner or null, if there is no such one.
    */
   private Pair<Goal,PosInOccurrence> findJoinPartner(
         Goal goal, PosInOccurrence pio, Services services) {
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
               if (isApplicable(g, gPio, false)) {
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
      
      return potentialPartners.head(); // TODO: Add option for choice later (maybe GUI)!
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
      if (formulae.size() == 1) {
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
    * @param u The update (in normal form) to extract program locations from.
    * @return All program locations (left sides) in the given update.
    */
   private HashSet<LocationVariable> getUpdateLocations(Term u) {
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

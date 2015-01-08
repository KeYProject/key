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
import de.uka.ilkd.key.java.JavaNonTerminalProgramElement;
import de.uka.ilkd.key.java.JavaProgramElement;
import de.uka.ilkd.key.java.NameAbstractionTable;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.visitor.CreatingASTVisitor;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.Visitor;
import de.uka.ilkd.key.logic.op.ElementaryUpdate;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.logic.op.UpdateJunctor;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.util.Pair;
import de.uka.ilkd.key.util.Triple;

//TODO: There is a problem with the Java program variables that
//      are declared inside a program; say there is a stmt "int x;",
//      then KeY introduces different constants x_1, x_2, ... in
//      the different branches. This leads to problems, e.g. in the
//      Path Condition construction in the ITE-Method.
//TODO: So far, the rule shall not be applied automatically,
//      since symbolic execution could be disturbed. In order
//      to prevent this, it is only applicable for *interactive*
//      goals, which is not very elegant. There should be a
//      different way to exclude the join rules from automatic
//      strategies....
//TODO: Check associated CloseAfterJoin rule, update if thesis
//      is updated.
//TODO: Make something as a progress bar for time consumptive
//      joins, like the IfThenElse join rule.

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
   public ImmutableList<Goal> apply(Goal goal, final Services services,
         RuleApp ruleApp) throws RuleAbortException {
      
      final TermBuilder tb = services.getTermBuilder();
      final PosInOccurrence pio = ruleApp.posInOccurrence();
      
      if (findPotentialJoinPartners(goal, pio) == null) {
         return null;
      }
      
      ImmutableList<Goal> newGoals = goal.split(1);
      
      final Goal newGoal = newGoals.head();
      
      // Find join partner
      ImmutableList<Pair<Goal, PosInOccurrence>> joinPartners = findJoinPartners(newGoal, pio);
      
      // Convert sequents to SE states
      ImmutableList<Pair<Term, Term>> joinPartnerStates = ImmutableSLList.nil();      
      for (Pair<Goal, PosInOccurrence> joinPartner : joinPartners) {
         Triple<Term, Term, Term> partnerSEState =
               sequentToSETriple(joinPartner.first, joinPartner.second, services);
         
         joinPartnerStates = joinPartnerStates.prepend(
               new Pair<Term, Term>(partnerSEState.first, partnerSEState.second));
      }
      
      Triple<Term, Term, Term> thisSEState =
            sequentToSETriple(newGoal, pio, services);
      joinPartnerStates = joinPartnerStates.prepend(
            new Pair<Term, Term>(thisSEState.first, thisSEState.second));
      
      Pair<Term, Term> joinedState = joinStates(joinPartnerStates, thisSEState.third, services);
      
      // Delete previous sequents      
      clearSemisequent(newGoal, true);
      clearSemisequent(newGoal, false);
      
      // Add new antecedent (path condition)
      SequentFormula newAntecedent = new SequentFormula(joinedState.second);
      newGoal.addFormula(
            newAntecedent,
            new PosInOccurrence(newAntecedent, PosInTerm.getTopLevel(), true));
      
      // Add new succedent (symbolic state & program counter)
      SequentFormula newSuccedent = new SequentFormula(
            tb.apply(joinedState.first, thisSEState.third));
      newGoal.addFormula(
            newSuccedent,
            new PosInOccurrence(newSuccedent, PosInTerm.getTopLevel(), false));
      
      // Close partner goals
      for (Pair<Goal, PosInOccurrence> joinPartner : joinPartners) {
         closeJoinPartnerGoal(newGoal.node(), joinPartner.first, joinedState, thisSEState.third);
      }
      
      return newGoals;
   }
   
   /**
    * Joins a list of SE states (U1,C1,p) and (U2,C2,p). p must
    * be the same in both states, so it is supplied separately.
    * 
    * @param states States to join.
    * @param services The services object.
    * @return A new joined SE state (U*,C*) which is a weakening
    *    of the original states.
    */
   protected abstract Pair<Term, Term> joinStates(
         ImmutableList<Pair<Term, Term>> states,
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
      // Note: Rule is deactivated for automatic application in
      //       JavaCardDLStrategy#computeCost(RuleApp, PosInOccurrence, Goal).
      //       This is a temporary workaround that removes the
      //       necessity to set goals to interactive. However,
      //       it would be nicer to obtain knowledge about whether
      //       or not this check for applicability originates from
      //       the user or from a strategy.
      
      return isApplicable(goal, pio,
            false, // Only permit interactive goals
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
    * @param term The term to extract program locations from.
    * @return All program locations in the given term.
    */
   protected HashSet<LocationVariable> getTermLocations(Term term) {
      final HashSet<LocationVariable> result =
            new HashSet<LocationVariable>();
      
      term.execPreOrder(new Visitor() {
         
         @Override
         public void visit(Term visited) {
            Operator op = visited.op();
            
            if (!op.isRigid() &&
                  op instanceof LocationVariable) {
               result.add((LocationVariable) op);
            }
         }
         
         @Override
         public void subtreeLeft(Term subtreeRoot) {}
         
         @Override
         public void subtreeEntered(Term subtreeRoot) {}
      });
      
      return result;
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
    * Closes the given partner goal, using the CloseAfterJoin rule.
    * 
    * @param joinNodeParent Parent of remaining join node.
    * @param joinPartner Partner goal to close.
    */
   private void closeJoinPartnerGoal(
         Node joinNodeParent, Goal joinPartner, Pair<Term, Term> joinState, Term pc) {
      
      Services services = joinNodeParent.proof().getServices();
      InitConfig initConfig = joinNodeParent.proof().getInitConfig();
      
      CloseAfterJoin closeRule = new CloseAfterJoin(joinNodeParent, joinState, pc);
      RuleApp app = closeRule.createApp(null, services);
      
      // Register rule if not done yet.
      // This avoids error messages of the form "no justification found for rule...".
      if (initConfig.getJustifInfo().getJustification(closeRule) == null) {
         initConfig.registerRuleIntroducedAtNode(app, joinPartner.node(), true);
      }

      joinPartner.apply(app);
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
         Goal goal, PosInOccurrence pio) {
      
      Services services = goal.proof().getServices();
      
      ImmutableList<Pair<Goal,PosInOccurrence>> potentialPartners =
            findPotentialJoinPartners(goal, pio);
      
      JoinPartnerSelectionDialog selectionDialog =
            new JoinPartnerSelectionDialog(goal, pio, potentialPartners, services);
      selectionDialog.setVisible(true);
      
      return selectionDialog.getChosen();
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
         if (!g.equals(goal) && !g.isLinked()) {
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
                  //  PVs are already declared. We therefore use an own method equalsModRenamingStrong.
                  //  In principle, the method matches all LocationVariable occurrences.
                  //  This can lead to wrong matches! However, this should NOT be a problem,
                  //  since PVs occurring in the post condition should be excluded by the
                  //  doNotMatch set. However, if strange things happen, here *could* be a reason.
                  
                  //TODO: Case to check: Same post condition, different Java blocks
                  //  (differing in variables that are NOT in post condition).
                  
                  JavaProgramElement ownProgramElem     = ownSEState.third.javaBlock().program();
                  JavaProgramElement partnerProgramElem = partnerSEState.third.javaBlock().program();
                  
                  Term ownPostCond     = ownSEState.third.sub(0);
                  Term partnerPostCond = partnerSEState.third.sub(0);
                  
                  HashSet<LocationVariable> doNotMatch = getTermLocations(ownPostCond);
                  
                  // Requirement: Same post condition, matching program parts
                  if (ownPostCond.equals(partnerPostCond) &&
                        equalsModRenamingStrong(
                           ownProgramElem,
                           partnerProgramElem,
                           null,
                           doNotMatch)) {
                     
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
   
   /**
    * An equalsModRenaming that does not only abstract from variable declarations, 
    * but from *all* LocationVariable occurrences. Usually, this is quite to strong
    * and can lead to wrong matches. However, when the doNotMatch parameter is wisely
    * used (LocationVariables of post condition, for example), there *should* not be
    * a problem here.
    * 
    * @see SourceElement#equalsModRenaming(SourceElement, NameAbstractionTable)}
    * @param se1 First element to check equality (mod renaming) for
    * @param se2 Second element to check equality (mod renaming) for
    * @param nat Table for storing name abstractions. May be null at first call.
    * @param doNotMatch Set of variables that should NOT be matched.
    * @return true iff source elements can be matched, ignoring variable names.
    */
   private static boolean equalsModRenamingStrong(
         SourceElement se1, SourceElement se2,
         NameAbstractionTable nat,
         HashSet<LocationVariable> doNotMatch) {
      
      if (nat == null) {
         nat = new NameAbstractionTable();
      }
      
      // Core part: Match location variables
      if (se1 instanceof LocationVariable && 
            se2 instanceof LocationVariable &&
            !doNotMatch.contains(se1) &&
            !doNotMatch.contains(se2)) {
         
         nat.add(se1, se2);
         return true;
         
      }
      
      if (!(se1 instanceof JavaNonTerminalProgramElement) ||
            !(se2 instanceof JavaNonTerminalProgramElement)) {
         // No children here, can delegate to normal method.
         return se1.equalsModRenaming(se2, nat);
      }
      
      final JavaNonTerminalProgramElement jnte1 =
            (JavaNonTerminalProgramElement) se1;
      final JavaNonTerminalProgramElement jnte2 =
            (JavaNonTerminalProgramElement) se2;

      if (jnte1.getChildCount() != jnte2.getChildCount()) {
         return false;
      }

      for (int i = 0, cc = jnte1.getChildCount(); i < cc; i++) {
         if (!equalsModRenamingStrong(jnte1.getChildAt(i), jnte2.getChildAt(i), nat, doNotMatch)) {
            return false;
         }
      }
      return true;
   }
}

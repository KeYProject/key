package de.uka.ilkd.key.rule;

import java.util.ArrayList;
import java.util.HashSet;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.visitor.CreatingASTVisitor;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.ElementaryUpdate;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.logic.op.UpdateJunctor;
import de.uka.ilkd.key.proof.Goal;

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
      
      Term newUpdate  = tb.parallel(newElementaryUpdates);
      Term newFormula = tb.apply(newUpdate, termAfterUpdate);
      
      // TODO: Check later:
      // it happened that after applying rule to one of
      // two top level sequents, one completely vanished
      // afterward. Fix!

      g.changeFormula(
            new SequentFormula(newFormula),
            pio);
      
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
      // We admit top level formulas of the form \<{ ... }\> phi
      // and U \<{ ... }\> phi, where U must be an update
      // in normal form, i.e. a parallel update of elementary
      // updates.
      
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
      
      public HashSet<LocationVariable> getVariables() {
         return variables;
      }
      
   }
}

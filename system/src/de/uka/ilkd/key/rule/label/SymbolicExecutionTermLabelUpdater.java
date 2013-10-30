package de.uka.ilkd.key.rule.label;

import java.util.Iterator;
import java.util.List;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.Rule;
import de.uka.ilkd.key.rule.UseOperationContractRule;
import de.uka.ilkd.key.rule.WhileInvariantRule;

public class SymbolicExecutionTermLabelUpdater implements TermLabelUpdater {
   private final Name termLabelNameToRemove;
   
   public SymbolicExecutionTermLabelUpdater(Name termLabelNameToRemove) {
      assert termLabelNameToRemove != null;
      this.termLabelNameToRemove = termLabelNameToRemove;
   }

   @Override
   public boolean isUpdateRequired(Term tacletTerm,
         PosInOccurrence applicationPosInOccurrence,
         Rule rule, Goal goal) {
      if (goal != null) {
         if (rule instanceof UseOperationContractRule &&
               (goal.node().getNodeInfo().getBranchLabel().startsWith("Pre") || 
                goal.node().getNodeInfo().getBranchLabel().startsWith("Null reference"))) {
            return true;
         }
         if (rule instanceof WhileInvariantRule &&
             goal.node().getNodeInfo().getBranchLabel().startsWith("Invariant Initially Valid")) {
            return true;
         }
         else {
            return false;
         }
      }
      else {
         return false;
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void updateLabels(Term tacletTerm, 
                            PosInOccurrence applicationPosInOccurrence, 
                            Term termToUpdate, 
                            Rule rule,
                            Goal goal,
                            List<TermLabel> newLabels) {
      Iterator<TermLabel> iter = newLabels.iterator();
      while (iter.hasNext()) {
         TermLabel next = iter.next();
         if (termLabelNameToRemove.equals(next.name())) {
            iter.remove();
         }
      }
   }
}

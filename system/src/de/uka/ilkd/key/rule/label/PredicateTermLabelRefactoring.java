package de.uka.ilkd.key.rule.label;

import java.util.List;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.label.PredicateTermLabel;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.SortedOperator;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.AbstractOperationPO;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.rule.Rule;
import de.uka.ilkd.key.rule.UseOperationContractRule;
import de.uka.ilkd.key.rule.WhileInvariantRule;

/**
 * The {@link TermLabelRefactoring} used to label predicates with a
 * {@link PredicateTermLabel} on applied loop invariants or operation contracts.
 * @author Martin Hentschel
 */
public class PredicateTermLabelRefactoring implements TermLabelRefactoring {
   /**
    * {@inheritDoc}
    */
   @Override
   public ImmutableList<Name> getSupportedRuleNames() {
      return ImmutableSLList.<Name>nil().append(UseOperationContractRule.INSTANCE.name())
                                        .append(WhileInvariantRule.INSTANCE.name());
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public RefactoringScope defineRefactoringScope(TermServices services, PosInOccurrence applicationPosInOccurrence, Term applicationTerm, Rule rule, Goal goal, Object hint, Term tacletTerm) {
      if (shouldRefactor(goal, hint)) {
         return RefactoringScope.APPLICATION_CHILDREN_AND_GRANDCHILDREN_SUBTREE;
      }
      else {
         return RefactoringScope.NONE;
      }
   }
   
   /**
    * Checks if the given hint requires a refactoring.
    * @param goal The {@link Goal}.
    * @param hint The hint to check.
    * @return {@code true} perform refactoring, {@code false} do not perform refactoring.
    */
   protected boolean shouldRefactor(Goal goal, Object hint) {
      if (goal != null) {
         Proof proof = goal.proof();
         if (WhileInvariantRule.INITIAL_INVARIANT_ONLY_HINT.equals(hint) ||
             WhileInvariantRule.FULL_INVARIANT_TERM_HINT.equals(hint) ||
             UseOperationContractRule.FINAL_PRE_TERM_HINT.equals(hint)) {
            ProofOblInput problem = proof.getServices().getSpecificationRepository().getProofOblInput(proof);
            if (problem instanceof AbstractOperationPO) {
               return ((AbstractOperationPO) problem).isAddSymbolicExecutionLabel();
            }
            else {
               return false;
            }
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
   public void refactoreLabels(Services services, 
                               PosInOccurrence applicationPosInOccurrence, 
                               Term applicationTerm, 
                               Rule rule, 
                               Goal goal, 
                               Object hint, 
                               Term tacletTerm, 
                               Term term, 
                               List<TermLabel> labels) {
      if (shouldRefactor(goal, hint)) {
         if (isPredicate(term)) {
            TermLabel existingLabel = term.getLabel(PredicateTermLabel.NAME);
            if (existingLabel == null) {
               int labelID = services.getCounter(PredicateTermLabel.PROOF_COUNTER_NAME).getCountPlusPlus();
               labels.add(new PredicateTermLabel(labelID));
            }
         }
      }
   }
   
   /**
    * Checks if the given {@link Term} is a predicate.
    * @param term The {@link Term} to check.
    * @return {@code true} is predicate, {@code false} is something else.
    */
   protected boolean isPredicate(Term term) {
      if (term.op() instanceof Junctor) {
         return term.op() == Junctor.TRUE || term.op() == Junctor.FALSE;
      }
      if (term.op() instanceof SortedOperator) {
         return ((SortedOperator) term.op()).sort() == Sort.FORMULA;
      }
      else {
         return false;
      }
   }
}

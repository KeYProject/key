package de.uka.ilkd.key.rule.label;

import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.label.PredicateTermLabel;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.label.TermLabelState;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.AbstractOperationPO;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.rule.Rule;
import de.uka.ilkd.key.rule.UseOperationContractRule;
import de.uka.ilkd.key.rule.WhileInvariantRule;
import de.uka.ilkd.key.symbolic_execution.PredicateEvaluationUtil;
import de.uka.ilkd.key.symbolic_execution.util.JavaUtil;

/**
 * The {@link TermLabelRefactoring} used to label predicates with a
 * {@link PredicateTermLabel} on applied loop invariants or operation contracts.
 * @author Martin Hentschel
 */
public class PredicateTermLabelRefactoring implements TermLabelRefactoring {
   public static final Name CONCRETE_AND_1 = new Name("concrete_and_1"); // TODO: Generalize concrete to label below updates
   public static final Name CONCRETE_AND_2 = new Name("concrete_and_2");
   public static final Name CONCRETE_AND_3 = new Name("concrete_and_3");
   public static final Name CONCRETE_AND_4 = new Name("concrete_and_4");
   public static final Name CONCRETE_EQ_1 = new Name("concrete_eq_1");
   public static final Name CONCRETE_EQ_2 = new Name("concrete_eq_2");
   public static final Name CONCRETE_EQ_3 = new Name("concrete_eq_3");
   public static final Name CONCRETE_EQ_4 = new Name("concrete_eq_4");
   public static final Name CONCRETE_IMPL_1 = new Name("concrete_impl_1");
   public static final Name CONCRETE_IMPL_2 = new Name("concrete_impl_2");
   public static final Name CONCRETE_IMPL_3 = new Name("concrete_impl_3");
   public static final Name CONCRETE_IMPL_4 = new Name("concrete_impl_4");
   public static final Name CONCRETE_NOT_1 = new Name("concrete_not_1");
   public static final Name CONCRETE_NOT_2 = new Name("concrete_not_2");
   public static final Name CONCRETE_OR_1 = new Name("concrete_or_1");
   public static final Name CONCRETE_OR_2 = new Name("concrete_or_2");
   public static final Name CONCRETE_OR_3 = new Name("concrete_or_3");
   public static final Name CONCRETE_OR_4 = new Name("concrete_or_4");
   
   /**
    * Key prefix used in {@link TermLabelState} to store that the inner most
    * label was already refactored on a given {@link Goal}.
    */
   private static final String INNER_MOST_PARENT_REFACTORED_PREFIX = "innerMostParentRefactoredAtGoal_";
   
   /**
    * {@inheritDoc}
    */
   @Override
   public ImmutableList<Name> getSupportedRuleNames() {
      return ImmutableSLList.<Name>nil().prepend(UseOperationContractRule.INSTANCE.name())
                                        .prepend(WhileInvariantRule.INSTANCE.name())
                                        .prepend(CONCRETE_AND_1)
                                        .prepend(CONCRETE_AND_2)
                                        .prepend(CONCRETE_AND_3)
                                        .prepend(CONCRETE_AND_4)
                                        .prepend(CONCRETE_EQ_1)
                                        .prepend(CONCRETE_EQ_2)
                                        .prepend(CONCRETE_EQ_3)
                                        .prepend(CONCRETE_EQ_4)
                                        .prepend(CONCRETE_IMPL_1)
                                        .prepend(CONCRETE_IMPL_2)
                                        .prepend(CONCRETE_IMPL_3)
                                        .prepend(CONCRETE_IMPL_4)
                                        .prepend(CONCRETE_NOT_1)
                                        .prepend(CONCRETE_NOT_2)
                                        .prepend(CONCRETE_OR_1)
                                        .prepend(CONCRETE_OR_2)
                                        .prepend(CONCRETE_OR_3)
                                        .prepend(CONCRETE_OR_4)
                                        .prepend(PredicateTermLabelUpdate.IF_THEN_ELSE_SPLIT)
                                        .prepend(PredicateTermLabelUpdate.ARRAY_LENGTH_NOT_NEGATIVE);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public RefactoringScope defineRefactoringScope(TermLabelState state,
                                                  Services services, 
                                                  PosInOccurrence applicationPosInOccurrence, 
                                                  Term applicationTerm, 
                                                  Rule rule, 
                                                  Goal goal, 
                                                  Object hint, 
                                                  Term tacletTerm) {
      if (shouldRefactorSpecificationApplication(goal, hint)) {
         return RefactoringScope.APPLICATION_CHILDREN_AND_GRANDCHILDREN_SUBTREE;
      }
      else if (PredicateTermLabelUpdate.IF_THEN_ELSE_SPLIT.equals(rule.name()) ||
               PredicateTermLabelUpdate.ARRAY_LENGTH_NOT_NEGATIVE.equals(rule.name())) {
         return RefactoringScope.APPLICATION_CHILDREN_AND_GRANDCHILDREN_SUBTREE_AND_PARENTS;
      }
      else if (applicationPosInOccurrence != null && isConcreteJunctor(rule)) {
         if (applicationTerm.op() instanceof UpdateApplication) {
            TermLabel existingLabel = applicationPosInOccurrence.subTerm().getLabel(PredicateTermLabel.NAME);
            if (existingLabel != null) {
               return RefactoringScope.APPLICATION_BELOW_UPDATES;
            }
            else {
               return RefactoringScope.NONE;
            }
         }
         else {
            return RefactoringScope.NONE; // If the application term is not an update the StayOnPredicateTermLabelPolicy ensures that the label is maintained.
         }
      }
      else {
         return RefactoringScope.NONE;
      }
   }
   
   /**
    * Checks if the given {@link Rule} is a concrete junctor operation.
    * @param rule The {@link Rule} to check.
    * @return {@code true} is concrete junctor operation, {@code false} is something else.
    */
   protected boolean isConcreteJunctor(Rule rule) {
      return CONCRETE_AND_1.equals(rule.name()) ||
             CONCRETE_AND_2.equals(rule.name()) ||
             CONCRETE_AND_3.equals(rule.name()) ||
             CONCRETE_AND_4.equals(rule.name()) ||
             CONCRETE_EQ_1.equals(rule.name()) ||
             CONCRETE_EQ_2.equals(rule.name()) ||
             CONCRETE_EQ_3.equals(rule.name()) ||
             CONCRETE_EQ_4.equals(rule.name()) ||
             CONCRETE_IMPL_1.equals(rule.name()) ||
             CONCRETE_IMPL_2.equals(rule.name()) ||
             CONCRETE_IMPL_3.equals(rule.name()) ||
             CONCRETE_IMPL_4.equals(rule.name()) ||
             CONCRETE_NOT_1.equals(rule.name()) ||
             CONCRETE_NOT_2.equals(rule.name()) ||
             CONCRETE_OR_1.equals(rule.name()) ||
             CONCRETE_OR_2.equals(rule.name()) ||
             CONCRETE_OR_3.equals(rule.name()) ||
             CONCRETE_OR_4.equals(rule.name());
   }
   
   /**
    * Checks if the given hint requires a refactoring.
    * @param goal The {@link Goal}.
    * @param hint The hint to check.
    * @return {@code true} perform refactoring, {@code false} do not perform refactoring.
    */
   protected boolean shouldRefactorSpecificationApplication(Goal goal, Object hint) {
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
   public void refactoreLabels(TermLabelState state,
                               Services services, 
                               PosInOccurrence applicationPosInOccurrence, 
                               Term applicationTerm, 
                               Rule rule, 
                               Goal goal, 
                               Object hint, 
                               Term tacletTerm, 
                               Term term, 
                               List<TermLabel> labels) {
      if (shouldRefactorSpecificationApplication(goal, hint)) {
         refactorSpecificationApplication(term, goal ,services, labels);
      }
      else if (PredicateTermLabelUpdate.IF_THEN_ELSE_SPLIT.equals(rule.name()) ||
               PredicateTermLabelUpdate.ARRAY_LENGTH_NOT_NEGATIVE.equals(rule.name())) {
         refactorInCaseOfNewIdRequired(state, goal, term, services, labels);
      }
      else if (isConcreteJunctor(rule)) {
         refactorConcreteJunctor(applicationPosInOccurrence, term, labels);
      }
   }
   
   /**
    * Refactors a specification application.
    * @param term The {@link Term} which is now refactored.
    * @param goal The optional {@link Goal} on which the {@link Term} to create will be used.
    * @param services The {@link Services} used by the {@link Proof} on which a {@link Rule} is applied right now.
    * @param labels The new labels the {@link Term} will have after the refactoring.
    */
   protected void refactorSpecificationApplication(Term term, 
                                                   Goal goal,
                                                   Services services, 
                                                   List<TermLabel> labels) {
      if (PredicateEvaluationUtil.isPredicate(term)) {
         TermLabel existingLabel = term.getLabel(PredicateTermLabel.NAME);
         if (existingLabel == null) {
            int labelID = services.getCounter(PredicateTermLabel.PROOF_COUNTER_NAME).getCountPlusPlus();
            int labelSubID = PredicateTermLabel.newLabelSubID(services, labelID);
            labels.add(new PredicateTermLabel(labelID, labelSubID));
         }
      }
   }
   
   /**
    * Refactors in case that the inner most label needs a new ID.
    * @param state The {@link TermLabelState} of the current rule application.
    * @param goal The optional {@link Goal} on which the {@link Term} to create will be used.
    * @param term The {@link Term} which is now refactored.
    * @param services The {@link Services} used by the {@link Proof} on which a {@link Rule} is applied right now.
    * @param labels The new labels the {@link Term} will have after the refactoring.
    */
   protected void refactorInCaseOfNewIdRequired(TermLabelState state, 
                                                Goal goal, 
                                                Term term, 
                                                Services services, 
                                                List<TermLabel> labels) {
      if (goal != null && !isInnerMostParentRefactored(state, goal)) {
         TermLabel existingLabel = term.getLabel(PredicateTermLabel.NAME);
         if (existingLabel instanceof PredicateTermLabel) {
            PredicateTermLabel pLabel = (PredicateTermLabel) existingLabel;
            int labelID = pLabel.getMajorId();
            int labelSubID = PredicateTermLabel.newLabelSubID(services, labelID);
            labels.remove(existingLabel);
            labels.add(new PredicateTermLabel(labelID, labelSubID, Collections.singletonList(pLabel.getId())));
            setInnerMostParentRefactored(state, goal, true);
         }
      }
   }
   
   /**
    * Refactors a concrete junctor application.
    * @param applicationPosInOccurrence The {@link PosInOccurrence} in the previous {@link Sequent} which defines the {@link Term} that is rewritten.
    * @param term The {@link Term} which is now refactored.
    * @param labels The new labels the {@link Term} will have after the refactoring.
    */
   protected void refactorConcreteJunctor(PosInOccurrence applicationPosInOccurrence, 
                                          Term term, 
                                          List<TermLabel> labels) {
      PredicateTermLabel applicationLabel = (PredicateTermLabel)applicationPosInOccurrence.subTerm().getLabel(PredicateTermLabel.NAME);
      PredicateTermLabel termLabel = (PredicateTermLabel)term.getLabel(PredicateTermLabel.NAME);
      if (termLabel == null) {
         labels.add(applicationLabel);
      }
      else {
         labels.remove(termLabel);
         Set<String> beforeIds = new LinkedHashSet<String>();
         JavaUtil.addAll(beforeIds, termLabel.getBeforeIds());
         beforeIds.add(applicationLabel.getId());
         labels.add(new PredicateTermLabel(termLabel.getMajorId(), termLabel.getMinorId(), beforeIds));
      }
   }
   
   /**
    * Checks if the inner most parent was already refactored on the given {@link Goal}.
    * @param state The {@link TermLabelState} to read from.
    * @param goal The {@link Goal} to check.
    * @return {@code true} already refactored, {@code false} not refactored yet.
    */
   public static boolean isInnerMostParentRefactored(TermLabelState state, Goal goal) {
      Map<Object, Object> labelState = state.getLabelState(PredicateTermLabel.NAME);
      return labelState.containsKey(INNER_MOST_PARENT_REFACTORED_PREFIX + goal.node().serialNr());
   }
   
   /**
    * Defines  if the inner most parent was already refactored on the given {@link Goal}.
    * @param state The {@link TermLabelState} to read from.
    * @param goal The {@link Goal} to check.
    * @param refactored {@code true} already refactored, {@code false} not refactored yet.
    */
   public static void setInnerMostParentRefactored(TermLabelState state, Goal goal, boolean refactored) {
      Map<Object, Object> labelState = state.getLabelState(PredicateTermLabel.NAME);
      labelState.put(INNER_MOST_PARENT_REFACTORED_PREFIX + goal.node().serialNr(), Boolean.valueOf(refactored));
   }
}

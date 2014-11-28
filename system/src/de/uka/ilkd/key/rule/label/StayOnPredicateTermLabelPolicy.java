package de.uka.ilkd.key.rule.label;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.label.PredicateTermLabel;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.Rule;
import de.uka.ilkd.key.rule.Taclet.TacletLabelHint;
import de.uka.ilkd.key.rule.Taclet.TacletLabelHint.TacletOperation;
import de.uka.ilkd.key.symbolic_execution.PredicateEvaluationUtil;
import de.uka.ilkd.key.symbolic_execution.util.IFilter;
import de.uka.ilkd.key.symbolic_execution.util.JavaUtil;

/**
 * This {@link TermLabelPolicy} maintains a {@link PredicateTermLabel} on predicates.
 * @author Martin Hentschel
 */
public class StayOnPredicateTermLabelPolicy implements TermLabelPolicy {
   /**
    * {@inheritDoc}
    */
   @Override
   public TermLabel keepLabel(Services services,
                              PosInOccurrence applicationPosInOccurrence, 
                              Term applicationTerm, 
                              Rule rule, 
                              Goal goal, 
                              Object hint, 
                              Term tacletTerm, 
                              Operator newTermOp, 
                              ImmutableArray<Term> newTermSubs, 
                              ImmutableArray<QuantifiableVariable> newTermBoundVars, 
                              JavaBlock newTermJavaBlock, 
                              ImmutableArray<TermLabel> newTermOriginalLabels,
                              TermLabel label) {
      label = ensureThatOriginalLabelIsMaintained(newTermOriginalLabels, label);
      assert label instanceof PredicateTermLabel;
      // Maintain label if new Term is a predicate
      if (PredicateEvaluationUtil.isPredicate(newTermOp)) {
         // May change sub ID if logical operators like junctors are used
         if (hint instanceof TacletLabelHint) {
            TacletLabelHint tacletHint = (TacletLabelHint) hint;
            boolean newLabelIdRequired = TacletOperation.ADD_ANTECEDENT.equals(tacletHint.getTacletOperation()) ||
                                         TacletOperation.ADD_SUCCEDENT.equals(tacletHint.getTacletOperation()) ||
                                         TacletOperation.REPLACE_TO_ANTECEDENT.equals(tacletHint.getTacletOperation()) ||
                                         TacletOperation.REPLACE_TO_SUCCEDENT.equals(tacletHint.getTacletOperation());
            if (!newLabelIdRequired) {
               if (tacletHint.getSequentFormula() != null) {
                  if (!PredicateEvaluationUtil.isPredicate(tacletHint.getSequentFormula())) {
                     newLabelIdRequired = true;
                  }
               }
               else if (tacletHint.getTerm() != null) {
                  if (!PredicateEvaluationUtil.isPredicate(tacletHint.getTerm())) {
                     newLabelIdRequired = true;
                  }
               }
            }
            // Replace label with a new one with increased sub ID.
            if (newLabelIdRequired) {
               PredicateTermLabel pLabel = (PredicateTermLabel) label;
               int labelSubID = services.getCounter(PredicateTermLabel.PROOF_COUNTER_SUB_PREFIX + pLabel.getMajorId()).getCountPlusPlus();
               if (isTopLevel(tacletHint, tacletTerm)) {
                  label = new PredicateTermLabel(pLabel.getMajorId(), labelSubID, pLabel.getId());
               }
               else {
                  label = new PredicateTermLabel(pLabel.getMajorId(), labelSubID);
               }
            }
         }
         return label;
      }
      else if (PredicateEvaluationUtil.isLogicOperator(newTermOp)) {
         if (hint instanceof TacletLabelHint) {
            PredicateTermLabel pLabel = (PredicateTermLabel) label;
            int labelSubID = services.getCounter(PredicateTermLabel.PROOF_COUNTER_SUB_PREFIX + pLabel.getMajorId()).getCountPlusPlus();
            if (isTopLevel((TacletLabelHint) hint, tacletTerm)) {
               return new PredicateTermLabel(pLabel.getMajorId(), labelSubID, pLabel.getId());
            }
            else {
               return new PredicateTermLabel(pLabel.getMajorId(), labelSubID);
            }
         }
         else {
            return label;
         }
      }
      else {
         return null;
      }
   }

   protected TermLabel ensureThatOriginalLabelIsMaintained(ImmutableArray<TermLabel> originalLabels, TermLabel newLabel) {
      TermLabel originalLabel = JavaUtil.search(originalLabels, new IFilter<TermLabel>() {
         @Override
         public boolean select(TermLabel element) {
            return element instanceof PredicateTermLabel;
         }
      });
      return originalLabel != null ? originalLabel : newLabel;
   }

   protected boolean isTopLevel(TacletLabelHint tacletHint, Term tacletTerm) {
      if (TacletOperation.REPLACE_TERM.equals(tacletHint.getTacletOperation())) {
         return tacletHint.getTerm() == tacletTerm;
      }
      else {
         return tacletHint.getSequentFormula().formula() == tacletTerm;
      }
   }
}

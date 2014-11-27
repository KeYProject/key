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
import de.uka.ilkd.key.logic.op.SortedOperator;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.Rule;
import de.uka.ilkd.key.rule.Taclet.TacletLabelHint;

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
                              TermLabel label) {
      assert label instanceof PredicateTermLabel;
      // Maintain label if new Term is a predicate
      if (PredicateTermLabelRefactoring.isPredicate(newTermOp)) {
         // May change sub ID if logical operators like junctors are used
         if (hint instanceof TacletLabelHint) {
            TacletLabelHint tacletHint = (TacletLabelHint) hint;
            boolean newLabelIdRequired = false;
            if (tacletHint.getSequentFormula() != null) {
               if (!PredicateTermLabelRefactoring.isPredicate(tacletHint.getSequentFormula())) {
                  newLabelIdRequired = true;
               }
            }
            else if (tacletHint.getTerm() != null) {
               if (!PredicateTermLabelRefactoring.isPredicate(tacletHint.getTerm())) {
                  newLabelIdRequired = true;
               }
            }
            // Replace label with a new one with increased sub ID.
            if (newLabelIdRequired) {
               PredicateTermLabel pLabel = (PredicateTermLabel) label;
               int labelSubID = services.getCounter(PredicateTermLabel.PROOF_COUNTER_SUB_PREFIX + pLabel.getId()).getCountPlusPlus();
               label = new PredicateTermLabel(pLabel.getId(), labelSubID);
            }
         }
         return label;
      }
      else {
         return null;
      }
   }
}

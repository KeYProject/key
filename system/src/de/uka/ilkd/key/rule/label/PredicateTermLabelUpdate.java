package de.uka.ilkd.key.rule.label;

import java.util.Collections;
import java.util.Set;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.label.PredicateTermLabel;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.label.TermLabelManager;
import de.uka.ilkd.key.logic.label.TermLabelState;
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
 * The {@link TermLabelUpdate} used to label predicates with a
 * {@link PredicateTermLabel} of add clauses which were not labeled before.
 * @author Martin Hentschel
 */
public class PredicateTermLabelUpdate implements TermLabelUpdate {
   /**
    * {@inheritDoc}
    */
   @Override
   public ImmutableList<Name> getSupportedRuleNames() {
      return null; // Support all rules.
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void updateLabels(TermLabelState state,
                            Services services, 
                            PosInOccurrence applicationPosInOccurrence, 
                            Term applicationTerm, 
                            Term modalityTerm, 
                            Rule rule, 
                            Goal goal, 
                            Object hint, 
                            Term tacletTerm, 
                            Operator newTermOp, 
                            ImmutableArray<Term> newTermSubs, 
                            ImmutableArray<QuantifiableVariable> newTermBoundVars, 
                            JavaBlock newTermJavaBlock, 
                            Set<TermLabel> labels) {
      if (hint instanceof TacletLabelHint) {
         TacletLabelHint tacletHint = (TacletLabelHint) hint;
         if ((TacletOperation.ADD_ANTECEDENT.equals(tacletHint.getTacletOperation()) ||
              TacletOperation.ADD_SUCCEDENT.equals(tacletHint.getTacletOperation())) &&
             (PredicateEvaluationUtil.isPredicate(newTermOp) ||
              PredicateEvaluationUtil.isLogicOperator(newTermOp, newTermSubs))) {
            if (getTermLabel(labels, PredicateTermLabel.NAME) == null) {
               TermLabel label = TermLabelManager.findInnerMostParentLabel(applicationPosInOccurrence, PredicateTermLabel.NAME);
               if (label instanceof PredicateTermLabel) {
                  PredicateTermLabel oldLabel = (PredicateTermLabel) label;
                  int labelSubID = PredicateTermLabel.newLabelSubID(services, oldLabel);
                  PredicateTermLabel newLabel = new PredicateTermLabel(oldLabel.getMajorId(), labelSubID, Collections.singletonList(oldLabel.getId()));
                  labels.add(newLabel);
                  // Let the PredicateTermLabelRefactoring perform the refactoring, see also PredicateTermLabelRefactoring#PARENT_REFACTORING_REQUIRED
                  PredicateTermLabelRefactoring.setParentRefactroingRequired(state, true);
               }
            }
         }
      }
   }

   /**
    * Returns the {@link TermLabel} with the given {@link Name}.
    * @param labels the {@link TermLabel}s to search in.
    * @param name The {@link Name} of the {@link TermLabel} to search.
    * @return The found {@link TermLabel} or {@code} null if no element was found.
    */
   protected TermLabel getTermLabel(Set<TermLabel> labels, final Name name) {
      return JavaUtil.search(labels, new IFilter<TermLabel>() {
         @Override
         public boolean select(TermLabel element) {
            return element != null && element.name().equals(name);
         }
      });
   }
}

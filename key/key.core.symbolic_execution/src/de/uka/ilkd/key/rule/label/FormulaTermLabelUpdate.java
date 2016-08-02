package de.uka.ilkd.key.rule.label;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.java.CollectionUtil;
import org.key_project.util.java.IFilter;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.label.FormulaTermLabel;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.label.TermLabelManager;
import de.uka.ilkd.key.logic.label.TermLabelState;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.IfFormulaInstantiation;
import de.uka.ilkd.key.rule.Rule;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.Taclet.TacletLabelHint;
import de.uka.ilkd.key.rule.Taclet.TacletLabelHint.TacletOperation;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.symbolic_execution.TruthValueTracingUtil;

/**
 * The {@link TermLabelUpdate} used to label predicates with a
 * {@link FormulaTermLabel} of add clauses which were not labeled before.
 * @author Martin Hentschel
 */
public class FormulaTermLabelUpdate implements TermLabelUpdate {
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
                            RuleApp ruleApp,
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
             (TruthValueTracingUtil.isPredicate(newTermOp) ||
              TruthValueTracingUtil.isLogicOperator(newTermOp, newTermSubs))) {
            if (getTermLabel(labels, FormulaTermLabel.NAME) == null) {
               TermLabel label = TermLabelManager.findInnerMostParentLabel(applicationPosInOccurrence, FormulaTermLabel.NAME);
               if (label instanceof FormulaTermLabel) {
                  FormulaTermLabel oldLabel = (FormulaTermLabel) label;
                  int labelSubID = FormulaTermLabel.newLabelSubID(services, oldLabel);
                  FormulaTermLabel newLabel = new FormulaTermLabel(oldLabel.getMajorId(), labelSubID, Collections.singletonList(oldLabel.getId()));
                  labels.add(newLabel);
                  // Let the PredicateTermLabelRefactoring perform the refactoring, see also PredicateTermLabelRefactoring#PARENT_REFACTORING_REQUIRED
                  FormulaTermLabelRefactoring.setParentRefactroingRequired(state, true);
               }
            }
         }
      }
      if (ruleApp instanceof TacletApp) {
         TacletApp ta = (TacletApp) ruleApp;
         if (ta.ifInstsComplete() && ta.ifFormulaInstantiations() != null) {
            Map<SequentFormula, FormulaTermLabel> ifLabels = new LinkedHashMap<SequentFormula, FormulaTermLabel>();
            for (IfFormulaInstantiation ifInst : ta.ifFormulaInstantiations()) {
               FormulaTermLabel ifLabel = StayOnFormulaTermLabelPolicy.searchFormulaTermLabel(ifInst.getConstrainedFormula().formula().getLabels());
               if (ifLabel != null) {
                  ifLabels.put(ifInst.getConstrainedFormula(), ifLabel);
               }
            }
            if (!ifLabels.isEmpty()) {
               if (TruthValueTracingUtil.isLogicOperator(newTermOp, newTermSubs)
//                   || TruthValueEvaluationUtil.isPredicate(newTermOp)
                   ) {
                  for (Entry<SequentFormula, FormulaTermLabel> ifEntry : ifLabels.entrySet()) {
                     FormulaTermLabel ifLabel = ifEntry.getValue();
                     int labelSubID = FormulaTermLabel.newLabelSubID(services, ifLabel);
                     FormulaTermLabel newLabel = new FormulaTermLabel(ifLabel.getMajorId(), labelSubID, Collections.singletonList(ifLabel.getId()));
                     labels.add(newLabel);
                     FormulaTermLabelRefactoring.addSequentFormulaToRefactor(state, ifEntry.getKey());
                  }
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
      return CollectionUtil.search(labels, new IFilter<TermLabel>() {
         @Override
         public boolean select(TermLabel element) {
            return element != null && element.name().equals(name);
         }
      });
   }
}

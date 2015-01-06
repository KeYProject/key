package de.uka.ilkd.key.rule.label;

import java.util.Collections;
import java.util.Set;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
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

/**
 * The {@link TermLabelUpdate} used to label predicates with a
 * {@link PredicateTermLabel} of add clauses which were not labeled before.
 * @author Martin Hentschel
 */
public class PredicateTermLabelUpdate implements TermLabelUpdate {
   public static final Name IF_THEN_ELSE_SPLIT = new Name("ifthenelse_split");
   
   /**
    * {@inheritDoc}
    */
   @Override
   public ImmutableList<Name> getSupportedRuleNames() {
      return ImmutableSLList.<Name>nil().append(IF_THEN_ELSE_SPLIT); // TODO: Support also other cut rules
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
         if (TacletOperation.ADD_ANTECEDENT.equals(tacletHint.getTacletOperation()) ||
             TacletOperation.ADD_SUCCEDENT.equals(tacletHint.getTacletOperation())) {
            TermLabel label = TermLabelManager.findInnerMostParentLabel(applicationPosInOccurrence, PredicateTermLabel.NAME);
            if (label instanceof PredicateTermLabel) {
               PredicateTermLabel oldLabel = (PredicateTermLabel) label;
//               PredicateTermLabel newLabel = PredicateTermLabel.getNewInnerMostLabel(state);
//               if (newLabel == null) {
                  int labelSubID = services.getCounter(PredicateTermLabel.PROOF_COUNTER_SUB_PREFIX + oldLabel.getMajorId()).getCountPlusPlus();
                  PredicateTermLabel newLabel = new PredicateTermLabel(oldLabel.getMajorId(), labelSubID, Collections.singletonList(oldLabel.getId()));
//                  PredicateTermLabel.setNewInnerMostLabel(state, newLabel, oldLabel);
//               }
               labels.add(newLabel);
            }
         }
      }
   }
}

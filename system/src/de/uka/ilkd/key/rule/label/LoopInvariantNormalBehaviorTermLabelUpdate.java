package de.uka.ilkd.key.rule.label;

import java.util.List;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.label.ParameterlessTermLabel;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.Rule;
import de.uka.ilkd.key.rule.WhileInvariantRule;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

/**
 * Makes sure that {@link ParameterlessTermLabel#LOOP_INVARIANT_NORMAL_BEHAVIOR_LABEL} is introduced
 * when a {@link WhileInvariantRule} is applied.
 * @author Martin Hentschel
 */
public class LoopInvariantNormalBehaviorTermLabelUpdate implements TermLabelUpdate {
   /**
    * {@inheritDoc}
    */
   @Override
   public ImmutableList<Name> getSupportedRuleNames() {
      return ImmutableSLList.<Name>nil().append(WhileInvariantRule.INSTANCE.name());
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void updateLabels(Services services,
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
                            List<TermLabel> labels) {
      if (rule instanceof WhileInvariantRule &&
          "LoopBodyImplication".equals(hint) &&
          SymbolicExecutionUtil.hasSymbolicExecutionLabel(modalityTerm)) {
         if (!labels.contains(ParameterlessTermLabel.LOOP_INVARIANT_NORMAL_BEHAVIOR_LABEL)) {
            labels.add(ParameterlessTermLabel.LOOP_INVARIANT_NORMAL_BEHAVIOR_LABEL);
         }
      }
   }
}
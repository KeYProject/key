package de.uka.ilkd.key.rule.label;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.Rule;

/**
 * This {@link TermLabelPolicy} maintains a {@link TermLabel} as long
 * the new {@link Term} has the same {@link Operator} as the
 * previous best matching {@link Term} from which it was created.
 * @author Martin Hentschel
 */
public class StayOnOperatorTermLabelPolicy implements TermLabelPolicy {
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean keepLabel(TermServices services,
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
      return applicationTerm != null && newTermOp == applicationTerm.op();
   }
}
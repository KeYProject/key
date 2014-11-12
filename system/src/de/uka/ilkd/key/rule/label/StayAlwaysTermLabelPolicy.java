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
 * This {@link TermLabelPolicy} always maintains a {@link TermLabel}.
 * @author Martin Hentschel
 */
public class StayAlwaysTermLabelPolicy implements TermLabelPolicy {
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
                            Operator newTermOp, ImmutableArray<Term> newTermSubs, 
                            ImmutableArray<QuantifiableVariable> newTermBoundVars, 
                            JavaBlock newTermJavaBlock, 
                            TermLabel label) {
      return true;
   }
}

package de.uka.ilkd.key.rule.label;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.Rule;


public class StayOnOperatorTermPolicy implements TermPolicy {
   @Override
   public boolean keepLabel(Term tacletTerm,
         PosInOccurrence applicationPosInOccurrence, Term applicationTerm, Term bestMatchTerm,
         Rule rule, Goal goal, Operator newTermOp,
         ImmutableArray<Term> newTermSubs,
         ImmutableArray<QuantifiableVariable> newTermBoundVars,
         JavaBlock newTermJavaBlock) {
      return bestMatchTerm != null && newTermOp == bestMatchTerm.op();
   }
}

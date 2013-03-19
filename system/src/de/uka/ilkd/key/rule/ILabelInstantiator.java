package de.uka.ilkd.key.rule;

import java.util.List;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.logic.ITermLabel;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;

public interface ILabelInstantiator {
   public List<ITermLabel> instantiateLabels(Term tacletTerm, 
         PosInOccurrence applicationPosInOccurrence,
         Term applicationTerm,
         Rule rule,
         Operator newTermOp, 
         ImmutableArray<Term> newTermSubs, 
         ImmutableArray<QuantifiableVariable> newTermBoundVars,
         JavaBlock newTermJavaBlock);
}

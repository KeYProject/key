package de.uka.ilkd.key.rule;

import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.logic.ITermLabel;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.SymbolicExecutionLabel;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;

public final class SELabelInstantiator implements ILabelInstantiator {
   public static final SELabelInstantiator INSTANCE = new SELabelInstantiator();

   private SELabelInstantiator() {
   }
   
   @Override
   public List<ITermLabel> instantiateLabels(Term tacletTerm,
         PosInOccurrence applicationPosInOccurrence, Term applicationTerm,
         Rule rule, Operator newTermOp, ImmutableArray<Term> newTermSubs,
         ImmutableArray<QuantifiableVariable> newTermBoundVars,
         JavaBlock newTermJavaBlock) {
      List<ITermLabel> instantiatedLabels = new LinkedList<ITermLabel>();
      if (applicationTerm != null) {
         applicationTerm = TermBuilder.DF.goBelowUpdates(applicationTerm);
         if (applicationTerm.containsLabel(SymbolicExecutionLabel.INSTANCE)) {
            if (newTermOp instanceof Modality) {
               instantiatedLabels.add(SymbolicExecutionLabel.INSTANCE);
            }
         }
      }
      return instantiatedLabels;
   }
}

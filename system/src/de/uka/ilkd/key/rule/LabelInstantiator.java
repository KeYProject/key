package de.uka.ilkd.key.rule;

import java.util.ArrayList;

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
import de.uka.ilkd.key.util.MiscTools;

public class LabelInstantiator {
   private PosInOccurrence applicationPosInOccurrence;
   
   private Rule rule;

   public LabelInstantiator(PosInOccurrence applicationPosInOccurrence, Rule rule) {
      this.applicationPosInOccurrence = applicationPosInOccurrence;
      this.rule = rule;
   }

   public Term getApplicationTerm() {
      return applicationPosInOccurrence != null ? applicationPosInOccurrence.subTerm() : null;
   }
   
   public ImmutableArray<ITermLabel> instantiateLabels(Term tacletTerm, 
                                                            Operator newTermOp, 
         ImmutableArray<Term> newTermSubs, 
         ImmutableArray<QuantifiableVariable> newTermBoundVars,
         JavaBlock newTermJavaBlock) {
      ArrayList<ITermLabel> instantiatedLabels = new ArrayList<ITermLabel>(10);
      Term applicationTerm = getApplicationTerm();
      if (applicationTerm != null) {
         applicationTerm = TermBuilder.DF.goBelowUpdates(applicationTerm);
         if (applicationTerm.containsLabel(SymbolicExecutionLabel.INSTANCE)) {
            if (newTermOp instanceof Modality) {
               instantiatedLabels.add(SymbolicExecutionLabel.INSTANCE);
            }
         }
      }
      return new ImmutableArray<ITermLabel>(instantiatedLabels);
   }
}

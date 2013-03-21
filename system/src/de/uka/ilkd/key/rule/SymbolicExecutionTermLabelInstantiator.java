package de.uka.ilkd.key.rule;

import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.logic.ITermLabel;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.SymbolicExecutionTermLabel;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;

/**
 * The {@link ITermLabelInstantiator} used during prove to define how a
 * {@link SymbolicExecutionTermLabel} is maintained.
 * @author Martin Hentschel
 */
public final class SymbolicExecutionTermLabelInstantiator implements ITermLabelInstantiator {
   /**
    * The only instance of this class.
    */
   public static final SymbolicExecutionTermLabelInstantiator INSTANCE = new SymbolicExecutionTermLabelInstantiator();

   /**
    * Constructor to forbid mulitple instances.
    */
   private SymbolicExecutionTermLabelInstantiator() {
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public List<ITermLabel> instantiateLabels(Term tacletTerm,
                                             PosInOccurrence applicationPosInOccurrence, 
                                             Term applicationTerm,
                                             Rule rule, 
                                             Operator newTermOp, 
                                             ImmutableArray<Term> newTermSubs,
                                             ImmutableArray<QuantifiableVariable> newTermBoundVars,
                                             JavaBlock newTermJavaBlock) {
      List<ITermLabel> instantiatedLabels = new LinkedList<ITermLabel>();
      if (applicationTerm != null) {
         applicationTerm = TermBuilder.DF.goBelowUpdates(applicationTerm);
         if (applicationTerm.containsLabel(SymbolicExecutionTermLabel.INSTANCE)) {
            if (newTermOp instanceof Modality) {
               instantiatedLabels.add(SymbolicExecutionTermLabel.INSTANCE);
            }
         }
      }
      return instantiatedLabels;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getName() {
      return SymbolicExecutionTermLabel.NAME;
   }
}

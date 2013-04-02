package de.uka.ilkd.key.rule;

import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.logic.ITermLabel;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;

/**
 * Provides the basic functionality of {@link ITermLabelInstantiator}s
 * which treat {@link ITermLabelInstantiator} added to modalities to 
 * track symbolic execution.
 * @author Martin Hentschel
 */
public abstract class AbstractSymbolicExecutionInstantiator implements ITermLabelInstantiator {
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
      if (newTermOp instanceof Modality) {
         if (applicationTerm != null) {
            applicationTerm = TermBuilder.DF.goBelowUpdates(applicationTerm);
            ITermLabel termLabel = getTermLabel(applicationTerm);
            if (termLabel != null && applicationTerm.containsLabel(termLabel)) {
               instantiatedLabels.add(termLabel);
            }
         }
      }
      return instantiatedLabels;
   }
   
   /**
    * Returns the {@link ITermLabel} to work with.
    * @param applicationTerm The {@link Term} to rewrite.
    * @return The {@link ITermLabel} to work with.
    */
   protected abstract ITermLabel getTermLabel(Term applicationTerm);
}

// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
//

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
import de.uka.ilkd.key.proof.Goal;

/**
 * Provides the basic functionality of {@link ITermLabelWorker}s
 * which treat {@link ITermLabelWorker} added to modalities to 
 * track symbolic execution.
 * @author Martin Hentschel
 */
public abstract class AbstractSymbolicExecutionInstantiator implements ITermLabelWorker {
   /**
    * {@inheritDoc}
    */
   @Override
   public List<ITermLabel> instantiateLabels(Term tacletTerm,
                                             PosInOccurrence applicationPosInOccurrence, 
                                             Term applicationTerm,
                                             Rule rule, 
                                             Goal goal,
                                             Operator newTermOp, 
                                             ImmutableArray<Term> newTermSubs,
                                             ImmutableArray<QuantifiableVariable> newTermBoundVars,
                                             JavaBlock newTermJavaBlock) {
      List<ITermLabel> instantiatedLabels = new LinkedList<ITermLabel>();
      if (checkOperator(newTermOp)) {
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
   
   protected boolean checkOperator(Operator newTermOp) {
      return newTermOp instanceof Modality;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public List<ITermLabel> updateLabels(Term tacletTerm, 
                                        PosInOccurrence applicationPosInOccurrence, 
                                        Term termToUpdate, 
                                        Rule rule,
                                        Goal goal) {
      if (rule instanceof UseOperationContractRule &&
          goal.node().getNodeInfo().getBranchLabel().startsWith("Pre")) {
         return null; // Throw symbolic execution labels away in pre branch of use operation contract rule
      }
      else {
         return keepLabels(termToUpdate);
      }
   }
   
   /**
    * Keeps the managed {@link ITermLabel} available via {@link #getTermLabel(Term)}
    * if available.
    * @param termToUpdate The {@link Term} to update.
    * @return The {@link ITermLabel}s to keep.
    */
   protected List<ITermLabel> keepLabels(Term termToUpdate) {
      List<ITermLabel> updatedLabels = new LinkedList<ITermLabel>();
      ITermLabel termLabel = getTermLabel(termToUpdate);
      if (termLabel != null && termToUpdate.containsLabel(termLabel)) {
          updatedLabels.add(termLabel);
      }
      return updatedLabels;
   }

   /**
    * Returns the {@link ITermLabel} to work with.
    * @param applicationTerm The {@link Term} to rewrite.
    * @return The {@link ITermLabel} to work with.
    */
   protected abstract ITermLabel getTermLabel(Term applicationTerm);
}
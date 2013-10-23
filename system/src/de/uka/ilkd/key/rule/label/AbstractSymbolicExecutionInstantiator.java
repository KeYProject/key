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

package de.uka.ilkd.key.rule.label;

import de.uka.ilkd.key.rule.Rule;
import de.uka.ilkd.key.rule.UseOperationContractRule;
import de.uka.ilkd.key.rule.WhileInvariantRule;

import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.logic.TermLabel;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.proof.Goal;

/**
 * Provides the basic functionality of {@link TermLabelInstantiator}s
 * which treat {@link TermLabelInstantiator} added to modalities to 
 * track symbolic execution.
 * @author Martin Hentschel
 */
public abstract class AbstractSymbolicExecutionInstantiator implements TermLabelInstantiator {
   /**
    * {@inheritDoc}
    */
   @Override
   public List<TermLabel> instantiateLabels(Term tacletTerm,
                                             PosInOccurrence applicationPosInOccurrence, 
                                             Term applicationTerm,
                                             Rule rule, 
                                             Goal goal,
                                             Operator newTermOp, 
                                             ImmutableArray<Term> newTermSubs,
                                             ImmutableArray<QuantifiableVariable> newTermBoundVars,
                                             JavaBlock newTermJavaBlock) {
      List<TermLabel> instantiatedLabels = new LinkedList<TermLabel>();
      if (checkOperator(newTermOp)) {
         if (applicationTerm != null) {
            applicationTerm = TermBuilder.DF.goBelowUpdates(applicationTerm);
            TermLabel termLabel = getTermLabel(applicationTerm);
            if (termLabel != null && applicationTerm.containsLabel(termLabel)) {
               instantiatedLabels.add(termLabel);
            }
         }
      }
      return instantiatedLabels;
   }
   
   /**
    * Checks if the {@link Operator} is supported.
    * @param newTermOp The {@link Operator} to check.
    * @return {@code true} is supported; add labels if required, {@code false} is not supported; add no labels
    */
   protected boolean checkOperator(Operator newTermOp) {
      return newTermOp instanceof Modality;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void updateLabels(Term tacletTerm, 
                            PosInOccurrence applicationPosInOccurrence, 
                            Term termToUpdate, 
                            Rule rule,
                            Goal goal,
                            List<TermLabel> newLabels) {
      // Remove label from the pre branch of the UseOperationContractRule
      if (rule instanceof UseOperationContractRule &&
          (goal.node().getNodeInfo().getBranchLabel().startsWith("Pre") || 
           goal.node().getNodeInfo().getBranchLabel().startsWith("Null reference"))) {
         TermLabel termLabel = getTermLabel(termToUpdate);
         if (termLabel != null) {
            newLabels.remove(termLabel);
         }
      }
      if (rule instanceof WhileInvariantRule &&
          goal.node().getNodeInfo().getBranchLabel().startsWith("Invariant Initially Valid")) {
         TermLabel termLabel = getTermLabel(termToUpdate);
         if (termLabel != null) {
            newLabels.remove(termLabel);
         }
      }
   }

   /**
    * Returns the {@link TermLabel} to work with.
    * @param applicationTerm The {@link Term} to rewrite.
    * @return The {@link TermLabel} to work with.
    */
   protected abstract TermLabel getTermLabel(Term applicationTerm);
}
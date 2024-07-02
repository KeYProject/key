// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.symbolic_execution.model.impl;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.NodeInfo;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionConstraint;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionStart;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionTermination;
import de.uka.ilkd.key.symbolic_execution.model.ITreeSettings;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

/**
 * The default implementation of {@link IExecutionStart}.
 * @author Martin Hentschel
 */
public class ExecutionStart extends AbstractExecutionNode<SourceElement> implements IExecutionStart {
   /**
    * The up to know discovered {@link IExecutionTermination}s.
    */
   private ImmutableList<IExecutionTermination> terminations = ImmutableSLList.nil();
   
   /**
    * Constructor.
    * @param settings The {@link ITreeSettings} to use.
    * @param proofNode The {@link Node} of KeY's proof tree which is represented by this {@link IExecutionNode}.
    */
   public ExecutionStart(ITreeSettings settings,
                         Node proofNode) {
      super(settings, proofNode);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected String lazyComputeName() {
      return DEFAULT_START_NODE_NAME;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected IExecutionConstraint[] lazyComputeConstraints() {
      return SymbolicExecutionUtil.createExecutionConstraints(this);
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public String getElementType() {
      return "Start";
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ImmutableList<IExecutionTermination> getTerminations() {
      return terminations;
   }
   
   /**
    * Registers the given {@link IExecutionTermination}.
    * @param termination The {@link IExecutionTermination} to register.
    */
   public void addTermination(IExecutionTermination termination) {
      if (termination != null) {
         terminations = terminations.append(termination);
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected PosInOccurrence lazyComputeModalityPIO() {
      return SymbolicExecutionUtil.findModalityWithMaxSymbolicExecutionLabelId(getProofNode().sequent());
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public SourceElement getActiveStatement() {
      Term modalityTerm = getModalityPIO().subTerm();
      SourceElement firstStatement = modalityTerm.javaBlock().program().getFirstElement();
      return NodeInfo.computeActiveStatement(firstStatement);
   }
   
   /**
    * Removes the given termination.
    * @param termination The termination to be deleted.
    * @author Anna Filighera
    */
   public void removeTermination(IExecutionTermination termination) {
      terminations = terminations.removeAll(termination);
   }
}
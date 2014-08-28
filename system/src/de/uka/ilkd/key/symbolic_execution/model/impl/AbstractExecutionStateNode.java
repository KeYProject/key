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

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.symbolic_execution.ExecutionNodeSymbolicLayoutExtractor;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionStateNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionVariable;
import de.uka.ilkd.key.symbolic_execution.model.ITreeSettings;
import de.uka.ilkd.key.symbolic_execution.object_model.ISymbolicEquivalenceClass;
import de.uka.ilkd.key.symbolic_execution.object_model.ISymbolicLayout;

/**
 * Provides a basic implementation of {@link IExecutionStateNode}.
 * @author Martin Hentschel
 */
public abstract class AbstractExecutionStateNode<S extends SourceElement> extends AbstractExecutionNode implements IExecutionStateNode<S> {
   /**
    * The variable value pairs of the current state.
    */
   private IExecutionVariable[] variables;
   
   /**
    * The used {@link ExecutionNodeSymbolicLayoutExtractor}.
    */
   private ExecutionNodeSymbolicLayoutExtractor layoutExtractor;
   
   /**
    * Constructor.
    * @param settings The {@link ITreeSettings} to use.
    * @param mediator The used {@link KeYMediator} during proof.
    * @param proofNode The {@link Node} of KeY's proof tree which is represented by this {@link IExecutionNode}.
    */
   public AbstractExecutionStateNode(ITreeSettings settings, KeYMediator mediator, Node proofNode) {
      super(settings, mediator, proofNode);
   }

   /**
    * {@inheritDoc}
    */
   @SuppressWarnings("unchecked")
   @Override
   public S getActiveStatement() {
      return (S)getProofNodeInfo().getActiveStatement();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public PositionInfo getActivePositionInfo() {
      return getActiveStatement().getPositionInfo();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IExecutionVariable[] getVariables() {
      synchronized (this) {
         if (variables == null) {
            variables = lazyComputeVariables();
         }
         return variables;
      }
   }

   /**
    * Computes the variables lazily when {@link #getVariables()} is 
    * called the first time.
    * @return The {@link IExecutionVariable}s of the current state.
    */
   protected abstract IExecutionVariable[] lazyComputeVariables();

   /**
    * Returns the used {@link ExecutionNodeSymbolicLayoutExtractor}.
    * @return The used {@link ExecutionNodeSymbolicLayoutExtractor}.
    * @throws ProofInputException Occurred Exception.
    */
   public ExecutionNodeSymbolicLayoutExtractor getLayoutExtractor() throws ProofInputException {
      synchronized (this) {
         if (layoutExtractor == null) {
            layoutExtractor = lazyComputeLayoutExtractor();
         }
         return layoutExtractor;
      }
   }

   /**
    * Instantiates the used {@link ExecutionNodeSymbolicLayoutExtractor} lazily
    * when {@link #getLayoutExtractor()} is called the first time.
    * @return The created {@link ExecutionNodeSymbolicLayoutExtractor}.
    * @throws ProofInputException Occurred Exception.
    */
   protected ExecutionNodeSymbolicLayoutExtractor lazyComputeLayoutExtractor() throws ProofInputException {
      ExecutionNodeSymbolicLayoutExtractor result = new ExecutionNodeSymbolicLayoutExtractor(this);
      result.analyse();
      return result;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public int getLayoutsCount() throws ProofInputException {
      return getLayoutExtractor().getLayoutsCount();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ISymbolicLayout getInitialLayout(int layoutIndex) throws ProofInputException {
      return getLayoutExtractor().getInitialLayout(layoutIndex);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ISymbolicLayout getCurrentLayout(int layoutIndex) throws ProofInputException {
      return getLayoutExtractor().getCurrentLayout(layoutIndex);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ImmutableList<ISymbolicEquivalenceClass> getLayoutsEquivalenceClasses(int layoutIndex) throws ProofInputException {
      return getLayoutExtractor().getEquivalenceClasses(layoutIndex);
   }
}
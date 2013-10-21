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

package de.uka.ilkd.key.symbolic_execution.model.impl;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.symbolic_execution.ExecutionNodeSymbolicConfigurationExtractor;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionStateNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionVariable;
import de.uka.ilkd.key.symbolic_execution.object_model.ISymbolicConfiguration;
import de.uka.ilkd.key.symbolic_execution.object_model.ISymbolicEquivalenceClass;

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
    * The used {@link ExecutionNodeSymbolicConfigurationExtractor}.
    */
   private ExecutionNodeSymbolicConfigurationExtractor configurationExtractor;
   
   /**
    * Constructor.
    * @param mediator The used {@link KeYMediator} during proof.
    * @param proofNode The {@link Node} of KeY's proof tree which is represented by this {@link IExecutionNode}.
    */
   public AbstractExecutionStateNode(KeYMediator mediator, Node proofNode) {
      super(mediator, proofNode);
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
    * Returns the used {@link ExecutionNodeSymbolicConfigurationExtractor}.
    * @return The used {@link ExecutionNodeSymbolicConfigurationExtractor}.
    * @throws ProofInputException Occurred Exception.
    */
   public ExecutionNodeSymbolicConfigurationExtractor getConfigurationExtractor() throws ProofInputException {
      synchronized (this) {
         if (configurationExtractor == null) {
            configurationExtractor = lazyComputeConfigurationExtractor();
         }
         return configurationExtractor;
      }
   }

   /**
    * Instantiates the used {@link ExecutionNodeSymbolicConfigurationExtractor} lazily
    * when {@link #getConfigurationExtractor()} is called the first time.
    * @return The created {@link ExecutionNodeSymbolicConfigurationExtractor}.
    * @throws ProofInputException Occurred Exception.
    */
   protected ExecutionNodeSymbolicConfigurationExtractor lazyComputeConfigurationExtractor() throws ProofInputException {
      ExecutionNodeSymbolicConfigurationExtractor result = new ExecutionNodeSymbolicConfigurationExtractor(this);
      result.analyse();
      return result;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public int getConfigurationsCount() throws ProofInputException {
      return getConfigurationExtractor().getConfigurationsCount();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ISymbolicConfiguration getInitialConfiguration(int configurationIndex) throws ProofInputException {
      return getConfigurationExtractor().getInitialConfiguration(configurationIndex);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ISymbolicConfiguration getCurrentConfiguration(int configurationIndex) throws ProofInputException {
      return getConfigurationExtractor().getCurrentConfiguration(configurationIndex);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ImmutableList<ISymbolicEquivalenceClass> getConfigurationsEquivalenceClasses(int configurationIndex) throws ProofInputException {
      return getConfigurationExtractor().getEquivalenceClasses(configurationIndex);
   }
}
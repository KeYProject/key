/*******************************************************************************
 * Copyright (c) 2014 Karlsruhe Institute of Technology, Germany
 *                    Technical University Darmstadt, Germany
 *                    Chalmers University of Technology, Sweden
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Technical University Darmstadt - initial API and implementation and/or initial documentation
 *******************************************************************************/

package org.key_project.sed.key.core.model;

import org.eclipse.core.runtime.Assert;
import org.eclipse.debug.core.DebugException;
import org.key_project.sed.core.model.ISEBranchCondition;
import org.key_project.sed.core.model.ISENode;
import org.key_project.sed.core.model.ISourcePathProvider;
import org.key_project.sed.core.model.impl.AbstractSEBranchCondition;
import org.key_project.sed.core.model.memory.SEMemoryBranchCondition;
import org.key_project.sed.key.core.util.KeYModelUtil;
import org.key_project.sed.key.core.util.LogUtil;

import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionBranchCondition;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.profile.SymbolicExecutionJavaProfile;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

/**
 * Implementation of {@link ISEBranchCondition} for the symbolic execution debugger (SED)
 * based on KeY.
 * @author Martin Hentschel
 */
public class KeYBranchCondition extends AbstractSEBranchCondition implements IKeYSENode<IExecutionBranchCondition> {
   /**
    * The {@link IExecutionBranchCondition} to represent by this debug node.
    */
   private final IExecutionBranchCondition executionNode;
   
   /**
    * The contained children.
    */
   private IKeYSENode<?>[] children;

   /**
    * The method call stack.
    */
   private IKeYSENode<?>[] callStack;
   
   /**
    * The constraints
    */
   private KeYConstraint[] constraints;
   
   /**
    * The contained KeY variables.
    */
   private KeYVariable[] variables;
   
   /**
    * The conditions under which a group ending in this node starts.
    */
   private SEMemoryBranchCondition[] groupStartConditions;
   
   /**
    * Constructor.
    * @param target The {@link KeYDebugTarget} in that this branch condition is contained.
    * @param parent The parent in that this node is contained as child.
    * @param thread The {@link KeYThread} in that this node is contained.
    * @param executionNode The {@link IExecutionBranchCondition} to represent by this debug node.
    */
   public KeYBranchCondition(KeYDebugTarget target, 
                             IKeYSENode<?> parent, 
                             KeYThread thread, 
                             IExecutionBranchCondition executionNode) throws DebugException {
      super(target, parent, thread);
      Assert.isNotNull(executionNode);
      this.executionNode = executionNode;
      target.registerDebugNode(this);
      initializeAnnotations();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public KeYThread getThread() {
      return (KeYThread)super.getThread();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public KeYDebugTarget getDebugTarget() {
      return (KeYDebugTarget)super.getDebugTarget();
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public IKeYSENode<?> getParent() throws DebugException {
      return (IKeYSENode<?>)super.getParent();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IKeYSENode<?>[] getChildren() throws DebugException {
      synchronized (this) { // Thread save execution is required because thanks lazy loading different threads will create different result arrays otherwise.
         IExecutionNode<?>[] executionChildren = executionNode.getChildren();
         if (children == null) {
            children = KeYModelUtil.createChildren(this, executionChildren);
         }
         else if (children.length != executionChildren.length) { // Assumption: Only new children are added, they are never replaced or removed
            children = KeYModelUtil.updateChildren(this, children, executionChildren);
         }
         return children;
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IExecutionBranchCondition getExecutionNode() {
      return executionNode;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getName() throws DebugException {
      try {
         if (executionNode.isBranchConditionComputed() || !executionNode.isDisposed()) {
            String additionalBranchLabel = executionNode.getAdditionalBranchLabel();
            if (additionalBranchLabel != null) {
               return additionalBranchLabel + ": " + executionNode.getName();
            }
            else {
               return executionNode.getName();
            }
         }
         else {
            return null;
         }
      }
      catch (ProofInputException e) {
         throw new DebugException(LogUtil.getLogger().createErrorStatus("Can't compute name.", e));
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getPathCondition() throws DebugException {
      try {
         return executionNode.getFormatedPathCondition();
      }
      catch (ProofInputException e) {
         throw new DebugException(LogUtil.getLogger().createErrorStatus("Can't compute path condition.", e));
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IKeYSENode<?>[] getCallStack() throws DebugException {
      synchronized (this) {
         if (callStack == null) {
            callStack = KeYModelUtil.createCallStack(getDebugTarget(), executionNode.getCallStack()); 
         }
         return callStack;
      }
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean hasConstraints() throws DebugException {
      return !isTerminated() && super.hasConstraints();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public KeYConstraint[] getConstraints() throws DebugException {
      synchronized (this) {
         if (constraints == null) {
            constraints = KeYModelUtil.createConstraints(this, executionNode);
         }
         return constraints;
      }
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean hasVariables() throws DebugException {
      try {
         return getDebugTarget().getLaunchSettings().isShowVariablesOfSelectedDebugNode() &&
                !executionNode.isDisposed() && 
                SymbolicExecutionUtil.canComputeVariables(executionNode, executionNode.getServices()) &&
                super.hasVariables();
      }
      catch (ProofInputException e) {
         throw new DebugException(LogUtil.getLogger().createErrorStatus(e));
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public KeYVariable[] getVariables() throws DebugException {
      synchronized (this) {
         if (variables == null) {
            variables = KeYModelUtil.createVariables(this, executionNode);
         }
         return variables;
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public int getLineNumber() throws DebugException {
      return -1;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public int getCharStart() throws DebugException {
      return -1;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public int getCharEnd() throws DebugException {
      return -1;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getSourcePath() {
      try {
         // Return source path of the parent which is not a branch condition.
         ISENode parent = getParent();
         while (parent != null && parent instanceof ISEBranchCondition) {
            parent = parent.getParent();
         }
         if (parent instanceof ISourcePathProvider) {
            return ((ISourcePathProvider) parent).getSourcePath();
         }
         else {
            return null;
         }
      }
      catch (DebugException e) {
         return null;
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public SEMemoryBranchCondition[] getGroupStartConditions() throws DebugException {
      synchronized (this) { // Thread save execution is required because thanks lazy loading different threads will create different result arrays otherwise.
         if (groupStartConditions == null) {
            groupStartConditions = KeYModelUtil.createCompletedBlocksConditions(this);
         }
         return groupStartConditions;
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void setParent(ISENode parent) {
      super.setParent(parent);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isTruthValueEvaluationEnabled() {
      return SymbolicExecutionJavaProfile.isTruthValueEvaluationEnabled(getExecutionNode().getProof());
   }
}
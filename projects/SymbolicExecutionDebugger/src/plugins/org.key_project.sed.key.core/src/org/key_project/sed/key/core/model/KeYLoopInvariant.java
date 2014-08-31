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
import org.eclipse.debug.core.model.IStackFrame;
import org.eclipse.jdt.core.dom.ASTNode;
import org.key_project.key4eclipse.starter.core.util.KeYUtil;
import org.key_project.key4eclipse.starter.core.util.KeYUtil.SourceLocation;
import org.key_project.sed.core.model.ISEDLoopInvariant;
import org.key_project.sed.core.model.impl.AbstractSEDLoopInvariant;
import org.key_project.sed.key.core.util.KeYModelUtil;
import org.key_project.sed.key.core.util.LogUtil;

import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionLoopInvariant;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

/**
 * Implementation of {@link ISEDLoopInvariant} for the symbolic execution debugger (SED)
 * based on KeY.
 * @author Martin Hentschel
 */
public class KeYLoopInvariant extends AbstractSEDLoopInvariant implements IKeYSEDDebugNode<IExecutionLoopInvariant> {
   /**
    * The {@link IExecutionLoopInvariant} to represent by this debug node.
    */
   private final IExecutionLoopInvariant executionNode;

   /**
    * The contained children.
    */
   private IKeYSEDDebugNode<?>[] children;

   /**
    * The source name.
    */
   private String sourceName;

   /**
    * The {@link SourceLocation} of this {@link IStackFrame}.
    */
   private SourceLocation sourceLocation;
   
   /**
    * The contained KeY variables.
    */
   private KeYVariable[] variables;
   
   /**
    * The constraints
    */
   private KeYConstraint[] constraints;

   /**
    * The method call stack.
    */
   private IKeYSEDDebugNode<?>[] callStack;

   /**
    * Constructor.
    * @param target The {@link KeYDebugTarget} in that this loop invariant is contained.
    * @param parent The parent in that this node is contained as child.
    * @param thread The {@link KeYThread} in that this node is contained.
    * @param executionNode The {@link IExecutionLoopInvariant} to represent by this debug node.
    */
   public KeYLoopInvariant(KeYDebugTarget target, 
                           IKeYSEDDebugNode<?> parent, 
                           KeYThread thread, 
                           IExecutionLoopInvariant executionNode) throws DebugException {
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
   public IKeYSEDDebugNode<?> getParent() throws DebugException {
      return (IKeYSEDDebugNode<?>)super.getParent();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IKeYSEDDebugNode<?>[] getChildren() throws DebugException {
      synchronized (this) { // Thread save execution is required because thanks lazy loading different threads will create different result arrays otherwise.
         IExecutionNode[] executionChildren = executionNode.getChildren();
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
   public IExecutionLoopInvariant getExecutionNode() {
      return executionNode;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getName() throws DebugException {
      try {
         return executionNode.getName();
      }
      catch (ProofInputException e) {
         throw new DebugException(LogUtil.getLogger().createErrorStatus("Can't compute name.", e));
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getSourcePath() {
      if (sourceName == null) {
         sourceName = SymbolicExecutionUtil.getSourcePath(computeGuardPositionInfo());
      }
      return sourceName;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public int getLineNumber() throws DebugException {
      if (sourceLocation == null) {
         sourceLocation = computeSourceLocation();
      }
      return sourceLocation.getLineNumber();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public int getCharStart() throws DebugException {
      if (sourceLocation == null) {
         sourceLocation = computeSourceLocation();
      }
      return sourceLocation.getCharStart();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public int getCharEnd() throws DebugException {
      if (sourceLocation == null) {
         sourceLocation = computeSourceLocation();
      }
      return sourceLocation.getCharEnd();
   }
   
   /**
    * Returns the {@link PositionInfo} of the guard, because it is always
    * the correct position even if it is reused in transformed while loops.
    * @return The {@link PositionInfo} of the guard.
    */
   protected PositionInfo computeGuardPositionInfo() {
      return executionNode.getLoopStatement().getGuardExpression().getPositionInfo();
   }
   
   /**
    * Computes the {@link SourceLocation} which values are returned via
    * {@link #getLineNumber()}, {@link #getCharStart()} and {@link #getCharEnd()}.
    * @return The computed {@link SourceLocation}.
    * @throws DebugException Occurred Exception.
    */
   protected SourceLocation computeSourceLocation() throws DebugException {
      SourceLocation guardLocation = KeYUtil.convertToSourceLocation(computeGuardPositionInfo());
      // Return location of loop using JDT
      ASTNode guardASTNode = KeYModelUtil.findASTNode(this, guardLocation);
      if (guardASTNode != null) {
         return KeYModelUtil.updateLocationFromAST(guardLocation, guardASTNode.getParent());
      }
      else {
         return guardLocation;
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
   public boolean canStepInto() {
      return getThread().canStepInto(this);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void stepInto() throws DebugException {
      getThread().stepInto(this);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean canStepOver() {
      return getThread().canStepOver(this);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void stepOver() throws DebugException {
      getThread().stepOver(this);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean canStepReturn() {
      return getThread().canStepReturn(this);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void stepReturn() throws DebugException {
      getThread().stepReturn(this);
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean canResume() {
      return getThread().canResume(this);
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void resume() throws DebugException {
      getThread().resume(this);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean canSuspend() {
      return getThread().canSuspend(this);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void suspend() throws DebugException {
      getThread().suspend(this);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IKeYSEDDebugNode<?>[] getCallStack() throws DebugException {
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
   public boolean isInitiallyValid() {
      return getExecutionNode().isInitiallyValid();
   }
}
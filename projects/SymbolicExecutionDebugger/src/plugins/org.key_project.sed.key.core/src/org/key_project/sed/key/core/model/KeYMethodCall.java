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
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jdt.core.ISourceRange;
import org.key_project.key4eclipse.starter.core.util.KeYUtil;
import org.key_project.key4eclipse.starter.core.util.KeYUtil.SourceLocation;
import org.key_project.sed.core.model.ISEDMethodCall;
import org.key_project.sed.core.model.ISEDThread;
import org.key_project.sed.core.model.impl.AbstractSEDMethodCall;
import org.key_project.sed.key.core.util.KeYModelUtil;
import org.key_project.sed.key.core.util.LogUtil;
import org.key_project.util.jdt.JDTUtil;

import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionMethodCall;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

/**
 * Implementation of {@link ISEDMethodCall} for the symbolic execution debugger (SED)
 * based on KeY.
 * @author Martin Hentschel
 */
public class KeYMethodCall extends AbstractSEDMethodCall implements IKeYSEDDebugNode<IExecutionMethodCall> {
   /**
    * The {@link IExecutionMethodCall} to represent by this debug node.
    */
   private final IExecutionMethodCall executionNode;

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
    * The method call stack.
    */
   private IKeYSEDDebugNode<?>[] callStack;

   /**
    * Constructor.
    * @param target The {@link KeYDebugTarget} in that this branch condition is contained.
    * @param parent The parent in that this node is contained as child.
    * @param thread The {@link ISEDThread} in that this node is contained.
    * @param executionNode The {@link IExecutionMethodCall} to represent by this debug node.
    */
   public KeYMethodCall(KeYDebugTarget target, 
                        IKeYSEDDebugNode<?> parent, 
                        ISEDThread thread, 
                        IExecutionMethodCall executionNode) throws DebugException {
      super(target, parent, thread);
      Assert.isNotNull(executionNode);
      this.executionNode = executionNode;
      initializeAnnotations();
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
   public IExecutionMethodCall getExecutionNode() {
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
         sourceName = SymbolicExecutionUtil.getSourcePath(executionNode.getProgramMethod().getPositionInfo());
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
    * Computes the {@link SourceLocation} which values are returned via
    * {@link #getLineNumber()}, {@link #getCharStart()} and {@link #getCharEnd()}.
    * @return The computed {@link SourceLocation}.
    * @throws DebugException Occurred Exception.
    */
   protected SourceLocation computeSourceLocation() throws DebugException {
      IProgramMethod explicitConstructor = executionNode.getExplicitConstructorProgramMethod();
      SourceLocation location = KeYUtil.convertToSourceLocation(explicitConstructor != null ?
                                                                     explicitConstructor.getPositionInfo() :
                                                                     executionNode.getProgramMethod().getPositionInfo());
      // Try to update the position info with the position of the method name provided by JDT.
      try {
         if (location.getCharEnd() >= 0) {
            ICompilationUnit compilationUnit = KeYModelUtil.findCompilationUnit(this);
            if (compilationUnit != null) {
               IMethod method = JDTUtil.findJDTMethod(compilationUnit, location.getCharEnd());
               if (method != null) {
                  ISourceRange range = method.getNameRange();
                  location = new SourceLocation(-1, range.getOffset(), range.getOffset() + range.getLength());
               }
            }
         }
         return location;
      }
      catch (Exception e) {
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
   public boolean hasVariables() throws DebugException {
      try {
         return getDebugTarget().getLaunchSettings().isShowVariablesOfSelectedDebugNode() &&
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
      return getDebugTarget().canStepInto(this);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void stepInto() throws DebugException {
      getDebugTarget().stepInto(this);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean canStepOver() {
      return getDebugTarget().canStepOver(this);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void stepOver() throws DebugException {
      getDebugTarget().stepOver(this);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean canStepReturn() {
      return getDebugTarget().canStepReturn(this);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void stepReturn() throws DebugException {
      getDebugTarget().stepReturn(this);
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean canResume() {
      return getDebugTarget().canResume(this);
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void resume() throws DebugException {
      getDebugTarget().resume(this);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean canSuspend() {
      return getDebugTarget().canSuspend(this);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void suspend() throws DebugException {
      getDebugTarget().suspend(this);
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
}
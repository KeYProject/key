package org.key_project.sed.key.core.model;

import org.eclipse.core.runtime.Assert;
import org.eclipse.debug.core.DebugException;
import org.eclipse.debug.core.model.IStackFrame;
import org.key_project.sed.core.model.ISEDStatement;
import org.key_project.sed.core.model.ISEDThread;
import org.key_project.sed.core.model.impl.AbstractSEDStatement;
import org.key_project.sed.key.core.util.KeYModelUtil;
import org.key_project.sed.key.core.util.LogUtil;
import org.key_project.sed.key.core.util.KeYModelUtil.SourceLocation;

import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionStatement;

/**
 * Implementation of {@link ISEDStatement} for the symbolic execution debugger (SED)
 * based on KeY.
 * @author Martin Hentschel
 */
public class KeYStatement extends AbstractSEDStatement implements IKeYSEDDebugNode<IExecutionStatement> {
   /**
    * The {@link IExecutionStatement} to represent by this debug node.
    */
   private IExecutionStatement executionNode;

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
    * Constructor.
    * @param target The {@link KeYDebugTarget} in that this branch condition is contained.
    * @param parent The parent in that this node is contained as child.
    * @param thread The {@link ISEDThread} in that this node is contained.
    * @param executionNode The {@link IExecutionStatement} to represent by this debug node.
    */
   public KeYStatement(KeYDebugTarget target, 
                       IKeYSEDDebugNode<?> parent, 
                       ISEDThread thread, 
                       IExecutionStatement executionNode) {
      super(target, parent, thread);
      Assert.isNotNull(executionNode);
      this.executionNode = executionNode;
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
      IExecutionNode[] executionChildren = executionNode.getChildren();
      if (children == null) {
         children = KeYModelUtil.createChildren(this, executionChildren);
      }
      else if (children.length != executionChildren.length) { // Assumption: Only new children are added, they are never replaced or removed
         children = KeYModelUtil.updateChildren(this, children, executionChildren);
      }
      return children;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IExecutionStatement getExecutionNode() {
      return executionNode;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getName() throws DebugException {
      return executionNode.getName();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getSourceName() {
      if (sourceName == null) {
         sourceName = KeYModelUtil.getSourceName(executionNode.getActivePositionInfo());
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
      SourceLocation location = KeYModelUtil.convertToSourceLocation(executionNode.getActivePositionInfo());
      return KeYModelUtil.updateLocationFromAST(this, location);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public KeYVariable[] getVariables() throws DebugException {
      if (variables == null) {
         variables = KeYModelUtil.createVariables(this, executionNode);
      }
      return variables;
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
}

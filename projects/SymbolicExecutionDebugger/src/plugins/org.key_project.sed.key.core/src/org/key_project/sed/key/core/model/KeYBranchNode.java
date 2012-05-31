package org.key_project.sed.key.core.model;

import org.eclipse.core.runtime.Assert;
import org.eclipse.debug.core.DebugException;
import org.eclipse.debug.core.model.IStackFrame;
import org.key_project.sed.core.model.ISEDBranchNode;
import org.key_project.sed.core.model.ISEDThread;
import org.key_project.sed.core.model.impl.AbstractSEDBranchNode;
import org.key_project.sed.key.core.util.KeYModelUtil;
import org.key_project.sed.key.core.util.KeYModelUtil.SourceLocation;

import de.uka.ilkd.key.symbolic_execution.model.IExecutionBranchNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;

/**
 * Implementation of {@link ISEDBranchNode} for the symbolic execution debugger (SED)
 * based on KeY.
 * @author Martin Hentschel
 */
public class KeYBranchNode extends AbstractSEDBranchNode implements IKeYSEDDebugNode<IExecutionBranchNode> {
   /**
    * The {@link IExecutionBranchNode} to represent by this debug node.
    */
   private IExecutionBranchNode executionNode;

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
    * @param executionNode The {@link IExecutionBranchNode} to represent by this debug node.
    */
   public KeYBranchNode(KeYDebugTarget target, 
                        IKeYSEDDebugNode<?> parent, 
                        ISEDThread thread, 
                        IExecutionBranchNode executionNode) {
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
   public IExecutionBranchNode getExecutionNode() {
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
}

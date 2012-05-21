package org.key_project.sed.key.core.model;

import org.eclipse.core.runtime.Assert;
import org.eclipse.debug.core.DebugException;
import org.key_project.sed.core.model.ISEDTermination;
import org.key_project.sed.core.model.ISEDThread;
import org.key_project.sed.core.model.impl.AbstractSEDTermination;
import org.key_project.sed.key.core.util.KeYModelUtil;

import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionTermination;

/**
 * Implementation of {@link ISEDTermination} for the symbolic execution debugger (SED)
 * based on KeY.
 * @author Martin Hentschel
 */
public class KeYTermination extends AbstractSEDTermination implements IKeYSEDDebugNode<IExecutionTermination> {
   /**
    * The {@link IExecutionTermination} to represent by this debug node.
    */
   private IExecutionTermination executionNode;

   /**
    * The contained children.
    */
   private IKeYSEDDebugNode<?>[] children;

   /**
    * Constructor.
    * @param target The {@link KeYDebugTarget} in that this branch condition is contained.
    * @param parent The parent in that this node is contained as child.
    * @param thread The {@link ISEDThread} in that this node is contained.
    * @param executionNode The {@link IExecutionTermination} to represent by this debug node.
    */
   public KeYTermination(KeYDebugTarget target, 
                         IKeYSEDDebugNode<?> parent, 
                         ISEDThread thread, 
                         IExecutionTermination executionNode) {
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
   public IExecutionTermination getExecutionNode() {
      return executionNode;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getName() throws DebugException {
      return executionNode.getName();
   }
}

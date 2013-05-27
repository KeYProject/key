package org.key_project.sed.core.model.memory;

import java.util.LinkedList;
import java.util.List;

import org.eclipse.debug.core.DebugException;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.ISEDLoopBodyTermination;
import org.key_project.sed.core.model.ISEDThread;
import org.key_project.sed.core.model.impl.AbstractSEDLoopBodyTermination;

/**
 * Implementation of {@link ISEDLoopBodyTermination} that stores all
 * information in the memory.
 * @author Martin Hentschel
 */
public class SEDMemoryLoopBodyTermination extends AbstractSEDLoopBodyTermination implements ISEDMemoryDebugNode {
   /**
    * The contained child nodes.
    */
   private List<ISEDDebugNode> children = new LinkedList<ISEDDebugNode>();
   
   /**
    * The name of this debug node.
    */
   private String name;
   
   /**
    * The human readable path condition to this node.
    */
   private String pathCondition;

   /**
    * The method call stack.
    */
   private ISEDDebugNode[] callStack;
   
   /**
    * Constructor.
    * @param target The {@link ISEDDebugTarget} in that this exceptional termination is contained.
    * @param parent The parent in that this node is contained as child.
    * @param thread The {@link ISEDThread} in that this exceptional termination is contained.
    */
   public SEDMemoryLoopBodyTermination(ISEDDebugTarget target, 
                                          ISEDDebugNode parent,
                                          ISEDThread thread) {
      super(target, parent, thread);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getName() throws DebugException {
      return name;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ISEDDebugNode[] getChildren() throws DebugException {
      return children.toArray(new ISEDDebugNode[children.size()]);
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void addChild(ISEDDebugNode child) {
      if (child != null) {
         children.add(child);
      }
   }

   /**
    * {@inheritDoc}
    */   
   @Override
   public void removeChild(ISEDDebugNode child) {
      if (child != null) {
         children.remove(child);
      }
   }

   /**
    * {@inheritDoc}
    */   
   @Override
   public void addChild(int index, ISEDDebugNode child) {
      if (child != null) {
         children.add(index, child);
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public int indexOfChild(ISEDDebugNode child) {
      if (child != null) {
         return children.indexOf(child);
      }
      else {
         return -1;
      }
   }
   
   /**
    * Sets the name of this node.
    * @param name the name to set.
    */
   public void setName(String name) {
      this.name = name;
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * Changed visibility to public.
    * </p>
    */
   @Override
   public void setId(String id) {
      super.setId(id);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getPathCondition() throws DebugException {
      return pathCondition;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void setPathCondition(String pathCondition) {
      this.pathCondition = pathCondition;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ISEDDebugNode[] getCallStack() throws DebugException {
      return callStack;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void setCallStack(ISEDDebugNode[] callStack) {
      this.callStack = callStack;
   }
}

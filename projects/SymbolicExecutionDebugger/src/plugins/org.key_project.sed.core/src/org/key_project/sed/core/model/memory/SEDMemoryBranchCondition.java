package org.key_project.sed.core.model.memory;

import java.util.LinkedList;
import java.util.List;

import org.eclipse.debug.core.DebugException;
import org.key_project.sed.core.model.ISEDBranchCondition;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.ISEDThread;
import org.key_project.sed.core.model.impl.AbstractSEDBranchCondition;

/**
 * Implementation of {@link ISEDBranchCondition} that stores all
 * information in the memory.
 * @author Martin Hentschel
 */
public class SEDMemoryBranchCondition extends AbstractSEDBranchCondition {
   /**
    * The contained child nodes.
    */
   private List<ISEDDebugNode> children = new LinkedList<ISEDDebugNode>();
   
   /**
    * Constructor.
    * @param target The {@link ISEDDebugTarget} in that this statement is contained.
    * @param thread The {@link ISEDThread} in that this statement is contained.
    */
   public SEDMemoryBranchCondition(ISEDDebugTarget target, ISEDThread thread) {
      super(target, thread);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ISEDDebugNode[] getChildren() throws DebugException {
      return children.toArray(new ISEDDebugNode[children.size()]);
   }
   
   /**
    * Adds a new {@link ISEDDebugNode} child node.
    * @param child The {@link ISEDDebugNode} to add.
    */
   public void addChild(ISEDDebugNode child) {
      if (child != null) {
         children.add(child);
      }
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
   public void setName(String name) {
      super.setName(name);
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
   public void setLineNumber(int lineNumber) {
      super.setLineNumber(lineNumber);
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
   public void setCharStart(int charStart) {
      super.setCharStart(charStart);
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
   public void setCharEnd(int charEnd) {
      super.setCharEnd(charEnd);
   }
}

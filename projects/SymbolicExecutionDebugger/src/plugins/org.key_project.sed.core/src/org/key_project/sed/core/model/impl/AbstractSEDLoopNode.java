package org.key_project.sed.core.model.impl;

import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.ISEDLoopNode;
import org.key_project.sed.core.model.ISEDThread;

/**
 * Provides a basic implementation of {@link ISEDLoopNode}.
 * @author Martin Hentschel
 * @see ISEDLoopNode
 */
public abstract class AbstractSEDLoopNode extends AbstractSEDStackFrameCompatibleDebugNode implements ISEDLoopNode {
   /**
    * Constructor.
    * @param target The {@link ISEDDebugTarget} in that this loop node is contained.
    * @param parent The parent in that this node is contained as child.
    * @param thread The {@link ISEDThread} in that this loop node is contained.
    */
   public AbstractSEDLoopNode(ISEDDebugTarget target, 
                                ISEDDebugNode parent,
                                ISEDThread thread) {
      super(target, parent, thread);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getNodeType() {
      return "Loop Node";
   }
}

package org.key_project.sed.core.model.impl;

import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.ISEDLoopCondition;
import org.key_project.sed.core.model.ISEDThread;

/**
 * Provides a basic implementation of {@link ISEDLoopCondition}.
 * @author Martin Hentschel
 * @see ISEDLoopCondition
 */
public abstract class AbstractSEDLoopCondition extends AbstractSEDStackFrameCompatibleDebugNode implements ISEDLoopCondition {
   /**
    * Constructor.
    * @param target The {@link ISEDDebugTarget} in that this loop condition is contained.
    * @param parent The parent in that this node is contained as child.
    * @param thread The {@link ISEDThread} in that this loop condition is contained.
    */
   public AbstractSEDLoopCondition(ISEDDebugTarget target, 
                                ISEDDebugNode parent,
                                ISEDThread thread) {
      super(target, parent, thread);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getNodeType() {
      return "Loop Condition";
   }
}

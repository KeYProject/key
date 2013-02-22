package org.key_project.sed.core.model.impl;

import org.key_project.sed.core.model.ISEDBranchCondition;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.ISEDThread;
import org.key_project.sed.core.model.ISEDUseLoopInvariant;

/**
 * Provides a basic implementation of {@link ISEDUseLoopInvariant}.
 * @author Martin Hentschel
 * @see ISEDBranchCondition
 */
public abstract class AbstractSEDUseLoopInvariant extends AbstractSEDStackFrameCompatibleDebugNode implements ISEDUseLoopInvariant {
   /**
    * Constructor.
    * @param target The {@link ISEDDebugTarget} in that this use loop invariant is contained.
    * @param parent The parent in that this node is contained as child.
    * @param thread The {@link ISEDThread} in that this node is contained.
    */
   public AbstractSEDUseLoopInvariant(ISEDDebugTarget target, 
                                          ISEDDebugNode parent,
                                          ISEDThread thread) {
      super(target, parent, thread);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getNodeType() {
      String kind = "Use Loop Invariant";
      if (isInitiallyValid()) {
         return kind;
      }
      else {
         return kind + " (Initially invalid)";
      }
   }
}

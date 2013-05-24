package org.key_project.sed.core.model.impl;

import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.ISEDLoopBodyTermination;
import org.key_project.sed.core.model.ISEDThread;

/**
 * Provides a basic implementation of {@link ISEDLoopBodyTermination}.
 * @author Martin Hentschel
 * @see ISEDLoopBodyTermination
 */
public abstract class AbstractSEDLoopBodyTermination extends AbstractSEDTermination implements ISEDLoopBodyTermination {
   /**
    * Constructor.
    * @param target The {@link ISEDDebugTarget} in that this exceptional termination is contained.
    * @param parent The parent in that this node is contained as child.
    * @param thread The {@link ISEDThread} in that this node is contained.
    */
   public AbstractSEDLoopBodyTermination(ISEDDebugTarget target, 
                                            ISEDDebugNode parent,
                                            ISEDThread thread) {
      super(target, parent, thread);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getNodeType() {
      return "Loop Body Termination";
   }
}

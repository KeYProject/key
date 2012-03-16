package org.key_project.sed.core.model.impl;

import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.ISEDStatement;
import org.key_project.sed.core.model.ISEDTermination;
import org.key_project.sed.core.model.ISEDThread;

/**
 * Provides a basic implementation of {@link ISEDTermination}.
 * @author Martin Hentschel
 * @see ISEDStatement
 */
public abstract class AbstractSEDTermination extends AbstractSEDStackFrameCompatibleDebugNode implements ISEDTermination {
   /**
    * Constructor.
    * @param target The {@link ISEDDebugTarget} in that this termination is contained.
    * @param parent The parent in that this node is contained as child.
    * @param thread The {@link ISEDThread} in that this termination is contained.
    */
   public AbstractSEDTermination(ISEDDebugTarget target, 
                                 ISEDDebugNode parent,
                                 ISEDThread thread) {
      super(target, parent, thread);
   }
}

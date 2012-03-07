package org.key_project.sed.core.model.impl;

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
    * @param thread The {@link ISEDThread} in that this termination is contained.
    */
   public AbstractSEDTermination(ISEDDebugTarget target, ISEDThread thread) {
      super(target, thread);
   }
}

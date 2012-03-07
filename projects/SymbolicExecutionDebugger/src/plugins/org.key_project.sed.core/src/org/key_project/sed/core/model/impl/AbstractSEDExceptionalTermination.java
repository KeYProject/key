package org.key_project.sed.core.model.impl;

import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.ISEDExceptionalTermination;
import org.key_project.sed.core.model.ISEDStatement;
import org.key_project.sed.core.model.ISEDThread;

/**
 * Provides a basic implementation of {@link ISEDExceptionalTermination}.
 * @author Martin Hentschel
 * @see ISEDStatement
 */
public abstract class AbstractSEDExceptionalTermination extends AbstractSEDStackFrameCompatibleDebugNode implements ISEDExceptionalTermination {
   /**
    * Constructor.
    * @param target The {@link ISEDDebugTarget} in that this exceptional termination is contained.
    * @param thread The {@link ISEDThread} in that this exceptional termination is contained.
    */
   public AbstractSEDExceptionalTermination(ISEDDebugTarget target, ISEDThread thread) {
      super(target, thread);
   }
}

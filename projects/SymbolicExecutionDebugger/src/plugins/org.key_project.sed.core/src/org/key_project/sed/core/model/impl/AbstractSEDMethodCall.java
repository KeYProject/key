package org.key_project.sed.core.model.impl;

import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.ISEDMethodCall;
import org.key_project.sed.core.model.ISEDStatement;
import org.key_project.sed.core.model.ISEDThread;

/**
 * Provides a basic implementation of {@link ISEDMethodCall}.
 * @author Martin Hentschel
 * @see ISEDStatement
 */
public abstract class AbstractSEDMethodCall extends AbstractSEDStackFrameCompatibleDebugNode implements ISEDMethodCall {
   /**
    * Constructor.
    * @param target The {@link ISEDDebugTarget} in that this method call is contained.
    * @param thread The {@link ISEDThread} in that this method call is contained.
    */
   public AbstractSEDMethodCall(ISEDDebugTarget target, ISEDThread thread) {
      super(target, thread);
   }
}

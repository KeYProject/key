package org.key_project.sed.core.model.impl;

import org.key_project.sed.core.model.ISEDBranchCondition;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.ISEDStatement;
import org.key_project.sed.core.model.ISEDThread;

/**
 * Provides a basic implementation of {@link ISEDBranchCondition}.
 * @author Martin Hentschel
 * @see ISEDStatement
 */
public abstract class AbstractSEDBranchCondition extends AbstractSEDStackFrameCompatibleDebugNode implements ISEDBranchCondition {
   /**
    * Constructor.
    * @param target The {@link ISEDDebugTarget} in that this branch condition is contained.
    * @param thread The {@link ISEDThread} in that this branch condition is contained.
    */
   public AbstractSEDBranchCondition(ISEDDebugTarget target, ISEDThread thread) {
      super(target, thread);
   }
}

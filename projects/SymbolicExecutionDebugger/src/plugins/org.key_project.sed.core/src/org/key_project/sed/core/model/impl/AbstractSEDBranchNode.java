package org.key_project.sed.core.model.impl;

import org.key_project.sed.core.model.ISEDBranchNode;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.ISEDStatement;
import org.key_project.sed.core.model.ISEDThread;

/**
 * Provides a basic implementation of {@link ISEDBranchNode}.
 * @author Martin Hentschel
 * @see ISEDStatement
 */
public abstract class AbstractSEDBranchNode extends AbstractSEDStackFrameCompatibleDebugNode implements ISEDBranchNode {
   /**
    * Constructor.
    * @param target The {@link ISEDDebugTarget} in that this branch node is contained.
    * @param thread The {@link ISEDThread} in that this branch node is contained.
    */
   public AbstractSEDBranchNode(ISEDDebugTarget target, ISEDThread thread) {
      super(target, thread);
   }
}

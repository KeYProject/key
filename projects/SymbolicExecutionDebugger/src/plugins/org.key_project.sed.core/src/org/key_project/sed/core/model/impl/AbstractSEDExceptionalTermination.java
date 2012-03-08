package org.key_project.sed.core.model.impl;

import org.key_project.sed.core.model.ISEDDebugNode;
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
    * @param parent The parent in that this node is contained as child.
    * @param thread The {@link ISEDThread} in that this exceptional termination is contained.
    */
   public AbstractSEDExceptionalTermination(ISEDDebugTarget target, 
                                            ISEDDebugNode parent,
                                            ISEDThread thread) {
      super(target, parent, thread);
   }
}

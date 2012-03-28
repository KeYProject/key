package org.key_project.sed.core.model.impl;

import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.ISEDMethodReturn;
import org.key_project.sed.core.model.ISEDStatement;
import org.key_project.sed.core.model.ISEDThread;

/**
 * Provides a basic implementation of {@link ISEDMethodReturn}.
 * @author Martin Hentschel
 * @see ISEDStatement
 */
public abstract class AbstractSEDMethodReturn extends AbstractSEDStackFrameCompatibleDebugNode implements ISEDMethodReturn {
   /**
    * Constructor.
    * @param target The {@link ISEDDebugTarget} in that this method return is contained.
    * @param parent The parent in that this node is contained as child.
    * @param thread The {@link ISEDThread} in that this method return is contained.
    */
   public AbstractSEDMethodReturn(ISEDDebugTarget target, 
                                  ISEDDebugNode parent,
                                  ISEDThread thread) {
      super(target, parent, thread);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getNodeType() {
      return "Method Return";
   }
}

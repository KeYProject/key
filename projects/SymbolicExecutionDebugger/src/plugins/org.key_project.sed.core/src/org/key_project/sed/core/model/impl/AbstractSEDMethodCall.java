package org.key_project.sed.core.model.impl;

import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.ISEDMethodCall;
import org.key_project.sed.core.model.ISEDThread;

/**
 * Provides a basic implementation of {@link ISEDMethodCall}.
 * @author Martin Hentschel
 * @see ISEDMethodCall
 */
public abstract class AbstractSEDMethodCall extends AbstractSEDStackFrameCompatibleDebugNode implements ISEDMethodCall {
   /**
    * Constructor.
    * @param target The {@link ISEDDebugTarget} in that this method call is contained.
    * @param parent The parent in that this node is contained as child.
    * @param thread The {@link ISEDThread} in that this method call is contained.
    */
   public AbstractSEDMethodCall(ISEDDebugTarget target, 
                                ISEDDebugNode parent,
                                ISEDThread thread) {
      super(target, parent, thread);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getNodeType() {
      return "Method Call";
   }
}

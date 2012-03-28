package org.key_project.sed.core.model.impl;

import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.ISEDStatement;
import org.key_project.sed.core.model.ISEDTermination;

/**
 * Provides a basic implementation of {@link ISEDTermination}.
 * @author Martin Hentschel
 * @see ISEDStatement
 */
public abstract class AbstractSEDTermination extends AbstractSEDTerminateCompatibleDebugNode implements ISEDTermination {
   /**
    * Constructor.
    * @param target The {@link ISEDDebugTarget} in that this termination is contained.
    * @param parent The parent in that this node is contained as child.
    */
   public AbstractSEDTermination(ISEDDebugTarget target, 
                                 ISEDDebugNode parent) {
      super(target, parent);
   }
}

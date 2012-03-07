package org.key_project.sed.core.model.impl;

import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDDebugTarget;

/**
 * Provides a basic implementation of {@link ISEDDebugNode}.
 * @author Martin Hentschel
 * @see ISEDDebugNode
 */
public abstract class AbstractSEDDebugNode extends AbstractSEDDebugElement implements ISEDDebugNode {
   /**
    * Constructor.
    * @param target The {@link ISEDDebugTarget} in that this node is contained.
    */
   public AbstractSEDDebugNode(ISEDDebugTarget target) {
      super(target);
   }
}

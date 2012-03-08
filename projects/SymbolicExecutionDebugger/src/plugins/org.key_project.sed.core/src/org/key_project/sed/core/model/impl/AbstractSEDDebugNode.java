package org.key_project.sed.core.model.impl;

import org.eclipse.debug.core.DebugException;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDDebugTarget;

/**
 * Provides a basic implementation of {@link ISEDDebugNode}.
 * @author Martin Hentschel
 * @see ISEDDebugNode
 */
public abstract class AbstractSEDDebugNode extends AbstractSEDDebugElement implements ISEDDebugNode {
   /**
    * The parent in that this node is contained as child.
    */
   private ISEDDebugNode parent;
   
   /**
    * Constructor.
    * @param target The {@link ISEDDebugTarget} in that this node is contained.
    * @param parent The parent in that this node is contained as child.
    */
   public AbstractSEDDebugNode(ISEDDebugTarget target, ISEDDebugNode parent) {
      super(target);
      this.parent = parent;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ISEDDebugNode getParent() throws DebugException {
      return parent;
   }
}

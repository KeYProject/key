package org.key_project.sed.core.model.impl;

import org.eclipse.debug.core.DebugException;
import org.eclipse.debug.core.model.ITerminate;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDDebugTarget;

/**
 * Provides a basic implementation of {@link ISEDDebugNode}s which
 * also realize the interface {@link ITerminate} for compatibility reasons
 * with the Eclipse debug API.
 * @author Martin Hentschel
 */
public abstract class AbstractSEDTerminateCompatibleDebugNode extends AbstractSEDDebugNode implements ITerminate {
   /**
    * Constructor.
    * @param target The {@link ISEDDebugTarget} in that this branch condition is contained.
    * @param parent The parent in that this node is contained as child.
    */
   public AbstractSEDTerminateCompatibleDebugNode(ISEDDebugTarget target, ISEDDebugNode parent) {
      super(target, parent);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean canTerminate() {
      return getDebugTarget().canTerminate();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isTerminated() {
      return getDebugTarget().isTerminated();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void terminate() throws DebugException {
      getDebugTarget().terminate();
   }
}

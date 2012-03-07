package org.key_project.sed.core.model.impl;

import org.eclipse.debug.core.model.DebugElement;
import org.key_project.sed.core.model.ISEDDebugElement;
import org.key_project.sed.core.model.ISEDDebugTarget;

/**
 * Provides a basic implementation of {@link ISEDDebugElement}.
 * @author Martin Hentschel
 * @see ISEDDebugElement
 */
public abstract class AbstractSEDDebugElement extends DebugElement implements ISEDDebugElement {
   /**
    * Constructor.
    * @param target The {@link ISEDDebugTarget} in that this element is contained.
    */
   public AbstractSEDDebugElement(ISEDDebugTarget target) {
      super(target);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ISEDDebugTarget getDebugTarget() {
      return (ISEDDebugTarget)super.getDebugTarget();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getModelIdentifier() {
      return getDebugTarget().getModelIdentifier();
   }
}

package org.key_project.sed.core.model.impl;

import org.key_project.sed.core.model.ISEDConstraint;
import org.key_project.sed.core.model.ISEDDebugTarget;

/**
 * Provides a basic implementation of {@link ISEDConstraint}.
 * @author Martin Hentschel
 * @see ISEDConstraint
 */
public abstract class AbstractSEDConstraint extends AbstractSEDDebugElement implements ISEDConstraint {
   /**
    * Constructor.
    * @param target The {@link ISEDDebugTarget} in that this element is contained.
    */
   public AbstractSEDConstraint(ISEDDebugTarget target) {
      super(target);
   }
}

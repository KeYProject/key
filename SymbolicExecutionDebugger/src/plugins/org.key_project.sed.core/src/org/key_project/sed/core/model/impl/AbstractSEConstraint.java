package org.key_project.sed.core.model.impl;

import org.key_project.sed.core.model.ISEConstraint;
import org.key_project.sed.core.model.ISEDebugTarget;

/**
 * Provides a basic implementation of {@link ISEConstraint}.
 * @author Martin Hentschel
 * @see ISEConstraint
 */
public abstract class AbstractSEConstraint extends AbstractSEDebugElement implements ISEConstraint {
   /**
    * Constructor.
    * @param target The {@link ISEDebugTarget} in that this element is contained.
    */
   public AbstractSEConstraint(ISEDebugTarget target) {
      super(target);
   }
}

package org.key_project.sed.core.model.impl;

import org.key_project.sed.core.model.ISEDebugTarget;
import org.key_project.sed.core.model.ISENodeLink;

/**
 * Provides a basic implementation of {@link ISENodeLink}.
 * @author Martin Hentschel
 * @see ISENodeLink
 */
public abstract class AbstractSENodeLink extends AbstractSEDebugElement implements ISENodeLink {
   /**
    * Constructor.
    * @param target The {@link ISEDebugTarget} in that this method return is contained.
    */
   public AbstractSENodeLink(ISEDebugTarget target) {
      super(target);
   }
}

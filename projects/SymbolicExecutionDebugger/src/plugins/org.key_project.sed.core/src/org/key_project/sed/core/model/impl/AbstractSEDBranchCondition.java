package org.key_project.sed.core.model.impl;

import org.key_project.sed.core.model.ISEDBranchCondition;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.ISEDStatement;

/**
 * Provides a basic implementation of {@link ISEDBranchCondition}.
 * @author Martin Hentschel
 * @see ISEDStatement
 */
public abstract class AbstractSEDBranchCondition extends AbstractSEDTerminateCompatibleDebugNode implements ISEDBranchCondition {
   /**
    * Constructor.
    * @param target The {@link ISEDDebugTarget} in that this branch condition is contained.
    * @param parent The parent in that this node is contained as child.
    */
   public AbstractSEDBranchCondition(ISEDDebugTarget target, 
                                     ISEDDebugNode parent) {
      super(target, parent);
   }
}

package org.key_project.sed.core.model.impl;

import org.key_project.sed.core.model.ISEDBranchCondition;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.ISEDThread;

/**
 * Provides a basic implementation of {@link ISEDBranchCondition}.
 * @author Martin Hentschel
 * @see ISEDBranchCondition
 */
public abstract class AbstractSEDBranchCondition extends AbstractSEDTerminateCompatibleDebugNode implements ISEDBranchCondition {
   /**
    * Constructor.
    * @param target The {@link ISEDDebugTarget} in that this branch condition is contained.
    * @param parent The parent in that this node is contained as child.
    * @param thread The {@link ISEDThread} in that this node is contained.
    */
   public AbstractSEDBranchCondition(ISEDDebugTarget target, 
                                     ISEDDebugNode parent,
                                     ISEDThread thread) {
      super(target, parent, thread);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getNodeType() {
      return "Branch Condition";
   }
}

package org.key_project.sed.core.model.impl;

import org.key_project.sed.core.model.ISEDBranchCondition;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.ISEDThread;
import org.key_project.sed.core.model.ISEDUseOperationContract;

/**
 * Provides a basic implementation of {@link ISEDUseOperationContract}.
 * @author Martin Hentschel
 * @see ISEDBranchCondition
 */
public abstract class AbstractSEDUseOperationContract extends AbstractSEDStackFrameCompatibleDebugNode implements ISEDUseOperationContract {
   /**
    * Constructor.
    * @param target The {@link ISEDDebugTarget} in that this use operation contract is contained.
    * @param parent The parent in that this node is contained as child.
    * @param thread The {@link ISEDThread} in that this node is contained.
    */
   public AbstractSEDUseOperationContract(ISEDDebugTarget target, 
                                          ISEDDebugNode parent,
                                          ISEDThread thread) {
      super(target, parent, thread);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getNodeType() {
      String kind = "Use Operation Contract";
      if (isPreconditionComplied()) {
         if (!hasNotNullCheck() || isNotNullCheckComplied()) {
            return kind;
         }
         else {
            return kind + " (Null Pointer Check failed)";
         }
      }
      else {
         if (!hasNotNullCheck() || isNotNullCheckComplied()) {
            return kind + " (Precondition Check failed)";
         }
         else {
            return kind + " (Precondition Check and Null Pointer Check failed)";
         }
      }
   }
}

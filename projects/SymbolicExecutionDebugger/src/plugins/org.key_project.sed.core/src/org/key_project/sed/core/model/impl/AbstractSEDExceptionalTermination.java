package org.key_project.sed.core.model.impl;

import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.ISEDExceptionalTermination;
import org.key_project.sed.core.model.ISEDStatement;

/**
 * Provides a basic implementation of {@link ISEDExceptionalTermination}.
 * @author Martin Hentschel
 * @see ISEDStatement
 */
public abstract class AbstractSEDExceptionalTermination extends AbstractSEDTermination implements ISEDExceptionalTermination {
   /**
    * Constructor.
    * @param target The {@link ISEDDebugTarget} in that this exceptional termination is contained.
    * @param parent The parent in that this node is contained as child.
    */
   public AbstractSEDExceptionalTermination(ISEDDebugTarget target, 
                                            ISEDDebugNode parent) {
      super(target, parent);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getNodeType() {
      return "Exceptional Termination";
   }
}

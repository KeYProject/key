package org.key_project.sed.key.core.symbolic_execution.model;

import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.SourceElement;

/**
 * A special {@link IExecutionNode} for nodes in the symbolic execution tree
 * which represents a statement in the code. Such nodes also have a state
 * (e.g. heap values).
 * @author Martin Hentschel
 */
public interface IExecutionStateNode<S extends SourceElement> extends IExecutionNode {
   /**
    * Returns the active statement which is executed in the code.
    * @return The active statement which is executed in the code.
    */
   public S getActiveStatement();
   
   /**
    * Returns the {@link PositionInfo} of {@link #getActiveStatement()}.
    * @return The {@link PositionInfo} of {@link #getActiveStatement()}.
    */
   public PositionInfo getActivePositionInfo();
}

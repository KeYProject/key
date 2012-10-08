package de.uka.ilkd.key.symbolic_execution.model;

import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.symbolic_execution.object_model.ISymbolicConfiguration;

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
   
   /**
    * Returns the variable value pairs of the current state.
    * @return The variable value pairs.
    */
   public IExecutionVariable[] getVariables();
   
   public int getConfigurationsCount() throws ProofInputException;
   
   public ISymbolicConfiguration getInitialConfiguration(int configurationIndex) throws ProofInputException;
   
   public ISymbolicConfiguration getCurrentConfiguration(int configurationIndex) throws ProofInputException;
}

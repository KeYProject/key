package de.uka.ilkd.key.symbolic_execution.model;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.symbolic_execution.model.impl.ExecutionVariable;

/**
 * <p>
 * A variable value pair contained in an {@link IExecutionStateNode}, e.g.
 * the method parameter {@code int x = 42}.
 * </p>
 * <p>
 * The default implementation is {@link ExecutionVariable} which
 * is instantiated lazily by the {@link IExecutionStateNode} implementations.
 * </p>
 * @author Martin Hentschel
 * @see IExecutionStateNode
 * @see ExecutionVariable
 */
public interface IExecutionVariable extends IExecutionElement {
   /**
    * Returns the {@link IProgramVariable} which contains the represented value.
    * @return The {@link IProgramVariable} which contains the represented value.
    */
   public IProgramVariable getProgramVariable();
   
   /**
    * Returns the value of the variable.
    * @return The value of the variable.
    */
   public Term getValue() throws ProofInputException;
   
   /**
    * Returns the value of the variable as human readable string representation.
    * @return The value of the variable as human readable string representation.
    */
   public String getValueString() throws ProofInputException;
   
   /**
    * Returns the type of the variable as human readable string.
    * @return The type of the variable as human readable string.
    */
   public String getTypeString() throws ProofInputException;
   
   /**
    * Returns the parent {@link IExecutionVariable}.
    * @return The parent {@link IExecutionVariable}.
    */
   public IExecutionVariable getParentVariable();
   
   /**
    * Returns contained child variables which forms complex data types.
    * @return The contained child variables.
    */
   public IExecutionVariable[] getChildVariables() throws ProofInputException;
   
   /**
    * Returns the index in the parent array if an array cell value is represented.
    * @return The index in the parent array or {@code -1} if no array cell value is represented.
    */
   public int getArrayIndex();
   
   /**
    * Checks if the current value is part of a parent array.
    * @return {@code true} is array cell value, {@code false} is a "normal" value.
    */
   public boolean isArrayIndex();
}

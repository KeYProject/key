package de.uka.ilkd.key.symbolic_execution.model;

import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.symbolic_execution.model.impl.ExecutionVariable;

/**
 * <p>
 * A variable value pair contained in an {@link IExecutionStateNode}, e.g.
 * the method parameter {@code int x = 42;} will have the variable value pair
 * {@code x = 42}. This class represents the variable ({@code x}) which is represented
 * while its values are reprented as child {@link IExecutionValue} instances.
 * </p>
 * <p>
 * The default implementation is {@link ExecutionVariable} which
 * is instantiated lazily by the {@link IExecutionStateNode} implementations.
 * </p>
 * @author Martin Hentschel
 * @see IExecutionStateNode
 * @see IExecutionValue
 * @see ExecutionVariable
 */
public interface IExecutionVariable extends IExecutionElement {
   /**
    * Returns the {@link IProgramVariable} which contains the represented value.
    * @return The {@link IProgramVariable} which contains the represented value.
    */
   public IProgramVariable getProgramVariable();
   
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
   
   /**
    * Returns the parent {@link IExecutionValue} if available.
    * @return The parent {@link IExecutionValue} if available and {@code null} otherwise.
    */
   public IExecutionValue getParentValue();
   
   /**
    * Returns the value of this {@link IExecutionVariable}.
    * @return The value of this {@link IExecutionVariable}.
    */
   public IExecutionValue getValue() throws ProofInputException;
}

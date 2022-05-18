package de.uka.ilkd.key.symbolic_execution.model;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.symbolic_execution.model.impl.ExecutionMethodReturn;
import de.uka.ilkd.key.symbolic_execution.model.impl.ExecutionMethodReturnValue;

/**
 * <p>
 * A return value of an {@link IExecutionMethodReturn}.
 * <p>
 * The default implementation is {@link ExecutionMethodReturnValue} which
 * is instantiated via a {@link ExecutionMethodReturn} instances.
 * </p> 
 * @author Martin Hentschel
 * @see ExecutionMethodReturn
 * @see ExecutionMethodReturnValue
 */
public interface IExecutionMethodReturnValue extends IExecutionElement {
   /**
    * Returns the return value.
    * @return The return value.
    * @throws ProofInputException Occurred Exception.
    */
   public Term getReturnValue() throws ProofInputException;
   
   /**
    * Returns the return value as human readable {@link String}.
    * @return The return value as human readable {@link String}.
    * @throws ProofInputException Occurred Exception.
    */
   public String getReturnValueString() throws ProofInputException;
   
   /**
    * Checks if a condition is available via {@link #getCondition()} 
    * under which this return value is returned.
    * @return {@code true} condition is available, {@code false} condition is not available.
    * @throws ProofInputException
    */
   public boolean hasCondition() throws ProofInputException;
   
   /**
    * Returns the optional condition under which the return value is valid.
    * @return The optional condition under which the return value is valid.
    * @throws ProofInputException Occurred Exception.
    */
   public Term getCondition() throws ProofInputException;
   
   /**
    * Returns the optional condition under which the return value is valid
    * as human readable {@link String}.
    * @return The optional condition as human readable {@link String}.
    * @throws ProofInputException Occurred Exception.
    */
   public String getConditionString() throws ProofInputException;
}
package de.uka.ilkd.key.symbolic_execution.model;

import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.symbolic_execution.SymbolicExecutionTreeBuilder;
import de.uka.ilkd.key.symbolic_execution.model.impl.ExecutionMethodReturn;

/**
 * <p>
 * A node in the symbolic execution tree which represents a method return,
 * e.g. {@code return 42}.
 * </p>
 * <p>
 * The default implementation is {@link ExecutionMethodReturn} which
 * is instantiated via a {@link SymbolicExecutionTreeBuilder} instance.
 * </p>
 * @author Martin Hentschel
 * @see SymbolicExecutionTreeBuilder
 * @see ExecutionMethodReturn
 */
public interface IExecutionMethodReturn extends IExecutionStateNode<SourceElement> {
   /**
    * A reference to the {@link IExecutionMethodCall} which is now returned.
    * @return The call of the now returned method.
    */
   public IExecutionMethodCall getMethodCall();
   
   /**
    * Returns the human readable node name including the return value ({@link #getReturnValue()}).
    * @return The human readable node name including the return value.
    * @throws ProofInputException Occurred Exception.
    */
   public String getNameIncludingReturnValue() throws ProofInputException;
   
   /**
    * Returns the return value.
    * @return The return value.
    * @throws ProofInputException Occurred Exception.
    */
   public Term getReturnValue() throws ProofInputException;
   
   /**
    * Returns the return value formated for the user.
    * @return The return value formated for the user.
    * @throws ProofInputException Occurred Exception.
    */
   public String getFormatedReturnValue() throws ProofInputException;
}

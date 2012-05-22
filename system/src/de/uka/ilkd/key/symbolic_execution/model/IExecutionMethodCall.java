package de.uka.ilkd.key.symbolic_execution.model;

import de.uka.ilkd.key.java.reference.MethodReference;
import de.uka.ilkd.key.java.statement.MethodBodyStatement;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.symbolic_execution.SymbolicExecutionTreeBuilder;
import de.uka.ilkd.key.symbolic_execution.model.impl.ExecutionMethodCall;

/**
 * <p>
 * A node in the symbolic execution tree which represents a method call,
 * e.g. {@code foo()}.
 * </p>
 * <p>
 * The default implementation is {@link ExecutionMethodCall} which
 * is instantiated via a {@link SymbolicExecutionTreeBuilder} instance.
 * </p>
 * @author Martin Hentschel
 * @see SymbolicExecutionTreeBuilder
 * @see ExecutionMethodCall
 */
public interface IExecutionMethodCall extends IExecutionStateNode<MethodBodyStatement> {
   /**
    * Returns the {@link MethodReference} instance of the called method.
    * @return The {@link MethodReference} of the called method.
    */
   public MethodReference getMethodReference();
   
   /**
    * Returns the called {@link ProgramMethod}.
    * @return The called {@link ProgramMethod}.
    */
   public ProgramMethod getProgramMethod();
}

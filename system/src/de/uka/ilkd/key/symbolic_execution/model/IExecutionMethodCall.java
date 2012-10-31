package de.uka.ilkd.key.symbolic_execution.model;

import de.uka.ilkd.key.java.reference.MethodReference;
import de.uka.ilkd.key.java.statement.MethodBodyStatement;
import de.uka.ilkd.key.logic.op.IProgramMethod;
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
    * Returns the called {@link IProgramMethod}.
    * @return The called {@link IProgramMethod}.
    */
   public IProgramMethod getProgramMethod();
   
   /**
    * Checks if an implicit constructor is called.
    * @return {@code true} implicit constructor is called, {@code false} method or explicit constructor is called.
    */
   public boolean isImplicitConstructor();
   
   /**
    * Returns a copy of the {@link MethodReference} which calls the
    * explicit constructor instead of the implicit constructor.
    * @return The {@link MethodReference} to the explicit constructor or {@code null} if no constructor is called.
    */
   public MethodReference getExplicitConstructorMethodReference();

   /**
    * Returns the explicit constructor.
    * @return The explicit constructor or {@code null} if no constructor is called.
    */
   public IProgramMethod getExplicitConstructorProgramMethod();
}

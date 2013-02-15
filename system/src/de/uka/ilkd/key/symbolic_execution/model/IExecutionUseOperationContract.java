package de.uka.ilkd.key.symbolic_execution.model;

import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.symbolic_execution.SymbolicExecutionTreeBuilder;
import de.uka.ilkd.key.symbolic_execution.model.impl.ExecutionUseOperationContract;

/**
 * <p>
 * A node in the symbolic execution tree which represents a use operation contract application.
 * </p>
 * <p>
 * The default implementation is {@link ExecutionUseOperationContract} which
 * is instantiated via a {@link SymbolicExecutionTreeBuilder} instance.
 * </p>
 * @author Martin Hentschel
 * @see SymbolicExecutionTreeBuilder
 * @see ExecutionUseOperationContract
 */
public interface IExecutionUseOperationContract extends IExecutionStateNode<SourceElement> {
   /**
    * Returns the applied {@link Contract}.
    * @return The applied {@link Contract}.
    */
   public Contract getContract();
   
   /**
    * Returns the {@link IProgramMethod} of the applied {@link Contract}.
    * @return The {@link IProgramMethod} of the applied {@link Contract}.
    */
   public IProgramMethod getContractProgramMethod();
   
   /**
    * Checks if the precondition is complied.
    * @return {@code true} precondition complied, {@code false} precondition not complied.
    */
   public boolean isPreconditionComplied(); 

   /**
    * Checks if a not null check is available (instance method) or not (static method or constructor).
    * @return {@code true} not null check available, {@code false} not null check is not available.
    */
   public boolean hasNotNullCheck();
   
   /**
    * Checks if the not null check is complied.
    * @return {@code true} not null check complied, {@code false} not null check not complied.
    */
   public boolean isNotNullCheckComplied();
}

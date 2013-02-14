package org.key_project.sed.core.model;

import org.eclipse.debug.core.model.IStackFrame;
import org.key_project.sed.core.model.impl.AbstractSEDUseOperationContract;
import org.key_project.sed.core.model.memory.SEDMemoryUseOperationContract;

/**
 * A node in the symbolic execution tree which represents a use of an operation contract.
 * <p>
 * Clients may implement this interface. It is recommended to subclass
 * from {@link AbstractSEDUseOperationContract} instead of implementing this
 * interface directly. {@link SEDMemoryUseOperationContract} is also a default
 * implementation that stores all values in the memory.
 * </p>
 * @author Martin Hentschel
 * @see ISEDDebugNode
 */
public interface ISEDUseOperationContract extends ISEDDebugNode, IStackFrame {
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

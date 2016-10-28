package de.uka.ilkd.key.symbolic_execution.model;

import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.symbolic_execution.SymbolicExecutionTreeBuilder;
import de.uka.ilkd.key.symbolic_execution.model.impl.ExecutionJoin;

/**
 * <p>
 * A node in the symbolic execution tree which represents a join.
 * </p>
 * <p>
 * The default implementation is {@link ExecutionJoin} which
 * is instantiated via a {@link SymbolicExecutionTreeBuilder} instance.
 * </p>
 * @author Martin Hentschel
 * @see SymbolicExecutionTreeBuilder
 * @see ExecutionJoin
 */
public interface IExecutionJoin extends IExecutionNode<SourceElement> {
   /**
    * Checks if the weakening is verified.
    * @return {@code true} is verified, {@code false} is not verified.
    */
   public boolean isWeakeningVerified();

   /**
    * Checks if the weakening verification is supported.
    * @return {@code true} supported, {@code false} not supported.
    */
   public boolean isWeakeningVerificationSupported();
}

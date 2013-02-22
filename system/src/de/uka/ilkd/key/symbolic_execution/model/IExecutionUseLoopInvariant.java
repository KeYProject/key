package de.uka.ilkd.key.symbolic_execution.model;

import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.statement.While;
import de.uka.ilkd.key.speclang.LoopInvariant;
import de.uka.ilkd.key.symbolic_execution.SymbolicExecutionTreeBuilder;
import de.uka.ilkd.key.symbolic_execution.model.impl.ExecutionUseLoopInvariant;

/**
 * <p>
 * A node in the symbolic execution tree which represents a loop invariant application.
 * </p>
 * <p>
 * The default implementation is {@link ExecutionUseLoopInvariant} which
 * is instantiated via a {@link SymbolicExecutionTreeBuilder} instance.
 * </p>
 * @author Martin Hentschel
 * @see SymbolicExecutionTreeBuilder
 * @see ExecutionUseLoopInvariant
 */
public interface IExecutionUseLoopInvariant extends IExecutionStateNode<SourceElement> {
   /**
    * Returns the used {@link LoopInvariant}.
    * @return The used {@link LoopInvariant}.
    */
   public LoopInvariant getLoopInvariant();
   
   /**
    * Returns the loop statement which is simulated by its loop invariant.
    * @return The loop statement which is simulated by its loop invariant.
    */
   public While getLoopStatement();
   
   /**
    * Checks if the loop invariant is initially valid.
    * @return {@code true} initially valid, {@code false} initially invalid.
    */
   public boolean isInitiallyValid();
}

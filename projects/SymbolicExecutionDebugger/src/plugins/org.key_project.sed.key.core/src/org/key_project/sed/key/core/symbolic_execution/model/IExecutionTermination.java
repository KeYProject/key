package org.key_project.sed.key.core.symbolic_execution.model;

import org.key_project.sed.key.core.symbolic_execution.SymbolicExecutionTreeBuilder;
import org.key_project.sed.key.core.symbolic_execution.model.impl.ExecutionTermination;

import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Proof;

/**
 * <p>
 * A node in the symbolic execution tree which represents the normal termination of a branch,
 * e.g. {@code <end>} in case of normal termination or {@code <uncaught java.lang.NullPointerException>}
 * in case of exceptional termination.
 * </p>
 * <p>
 * The default implementation is {@link ExecutionTermination} which
 * is instantiated via a {@link SymbolicExecutionTreeBuilder} instance.
 * </p>
 * @author Martin Hentschel
 * @see SymbolicExecutionTreeBuilder
 * @see ExecutionTermination
 */
public interface IExecutionTermination extends IExecutionNode {
   /**
    * The default name of a termination node.
    */
   public static final String DEFAULT_TERMINATION_NODE_NAME = INTERNAL_NODE_NAME_START + "end" + INTERNAL_NODE_NAME_END;

   /**
    * Returns the {@link IProgramVariable} which is used in the {@link Sequent}
    * of {@link Proof#root()} to check if a normal or exceptional termination
    * occurred.
    * @return The {@link IProgramVariable} which is used to caught global exceptions.
    */
   public IProgramVariable getExceptionVariable();
   
   /**
    * Returns the {@link Sort} of the caught exception.
    * @return The {@link Sort} of the caught exception.
    */
   public Sort getExceptionSort();
   
   /**
    * Checks if a normal or an exceptional termination occurred.
    * @return {@code true} exceptional termination, {@code false} normal termination.
    */
   public boolean isExceptionalTermination();
}

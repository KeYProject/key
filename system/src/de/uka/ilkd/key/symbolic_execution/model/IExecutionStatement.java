package de.uka.ilkd.key.symbolic_execution.model;

import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.symbolic_execution.SymbolicExecutionTreeBuilder;
import de.uka.ilkd.key.symbolic_execution.model.impl.ExecutionStatement;

/**
 * <p>
 * A node in the symbolic execution tree which represents a single statement,
 * e.g. {@code int x =  1 + 2;}.
 * </p>
 * <p>
 * The default implementation is {@link ExecutionStatement} which
 * is instantiated via a {@link SymbolicExecutionTreeBuilder} instance.
 * </p>
 * @author Martin Hentschel
 * @see SymbolicExecutionTreeBuilder
 * @see ExecutionStatement
 */
public interface IExecutionStatement extends IExecutionStateNode<SourceElement> {
}

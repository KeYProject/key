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
}

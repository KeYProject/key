package org.key_project.sed.key.core.symbolic_execution.model;

import org.key_project.sed.key.core.symbolic_execution.SymbolicExecutionTreeBuilder;
import org.key_project.sed.key.core.symbolic_execution.model.impl.ExecutionLoopNode;

import de.uka.ilkd.key.java.statement.LoopStatement;

/**
 * <p>
 * A node in the symbolic execution tree which represents a loop.
 * e.g. {@code while(x >= 0)}. The loop condition ({@code x >= 0}) itself 
 * is represented as {@link IExecutionLoopCondition} instance.
 * </p>
 * <p>
 * The default implementation is {@link ExecutionLoopNode} which
 * is instantiated via a {@link SymbolicExecutionTreeBuilder} instance.
 * </p>
 * @author Martin Hentschel
 * @see SymbolicExecutionTreeBuilder
 * @see ExecutionLoopNode
 */
public interface IExecutionLoopNode extends IExecutionStateNode<LoopStatement> {
}

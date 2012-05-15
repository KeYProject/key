package org.key_project.sed.key.core.symbolic_execution.model;

import org.key_project.sed.core.model.ISEDBranchCondition;
import org.key_project.sed.key.core.symbolic_execution.SymbolicExecutionTreeBuilder;
import org.key_project.sed.key.core.symbolic_execution.model.impl.ExecutionBranchNode;

import de.uka.ilkd.key.java.statement.BranchStatement;

/**
 * <p>
 * A node in the symbolic execution tree which represents a node which
 * creates multiple child branches defined by branch conditions ({@link ISEDBranchCondition}),
 * e.g. {@code if(x >= 0)}.
 * </p>
 * <p>
 * The default implementation is {@link ExecutionBranchNode} which
 * is instantiated via a {@link SymbolicExecutionTreeBuilder} instance.
 * </p>
 * @author Martin Hentschel
 * @see SymbolicExecutionTreeBuilder
 * @see ExecutionBranchNode
 */
public interface IExecutionBranchNode extends IExecutionStateNode<BranchStatement> {
}

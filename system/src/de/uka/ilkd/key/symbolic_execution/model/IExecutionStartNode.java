package de.uka.ilkd.key.symbolic_execution.model;

import de.uka.ilkd.key.symbolic_execution.SymbolicExecutionTreeBuilder;
import de.uka.ilkd.key.symbolic_execution.model.impl.ExecutionStartNode;

/**
 * <p>
 * The start node of a symbolic execution tree.
 * </p>
 * <p>
 * The default implementation is {@link ExecutionStartNode} which
 * is instantiated via a {@link SymbolicExecutionTreeBuilder} instance.
 * </p>
 * @author Martin Hentschel
 * @see SymbolicExecutionTreeBuilder
 * @see ExecutionStartNode
 */
public interface IExecutionStartNode extends IExecutionNode {
   /**
    * The default name of a start node.
    */
   public static final String DEFAULT_START_NODE_NAME = INTERNAL_NODE_NAME_START + "start" + INTERNAL_NODE_NAME_END;
}

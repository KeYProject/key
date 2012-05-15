package org.key_project.sed.key.core.symbolic_execution.model;

import org.key_project.sed.key.core.symbolic_execution.SymbolicExecutionTreeBuilder;
import org.key_project.sed.key.core.symbolic_execution.model.impl.ExecutionStatement;

import de.uka.ilkd.key.java.SourceElement;

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

package org.key_project.sed.key.core.model;

import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;

/**
 * An {@link IKeYSEDDebugNode} which represents termination.
 * @author Martin Hentschel
 */
public interface IKeYTerminationNode<E extends IExecutionNode<?>> extends IKeYSEDDebugNode<E> {
}

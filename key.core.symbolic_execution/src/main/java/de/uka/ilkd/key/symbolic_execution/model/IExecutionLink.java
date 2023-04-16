package de.uka.ilkd.key.symbolic_execution.model;

/**
 * A link between two {@link IExecutionNode}s.
 *
 * @author Martin Hentschel
 */
public interface IExecutionLink {
    /**
     * Returns the source.
     *
     * @return The source.
     */
    IExecutionNode<?> getSource();

    /**
     * Returns the target.
     *
     * @return The target.
     */
    IExecutionNode<?> getTarget();
}

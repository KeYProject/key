package org.key_project.util.collection;

/**
 * Graph edge for use in a {@link Graph}.
 *
 * @author Arne Keller
 */
public interface GraphEdge {
    /**
     * @return where this edge starts
     */
    Object getSource();

    /**
     * @return where this edge goes to
     */
    Object getTarget();

    /**
     * Specify the source of this edge.
     *
     * @param source source node
     */
    void setSource(Object source);

    /**
     * Specify the target of this edge.
     *
     * @param target target node
     */
    void setTarget(Object target);
}

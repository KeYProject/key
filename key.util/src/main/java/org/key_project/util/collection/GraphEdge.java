package org.key_project.util.collection;

/**
 * Graph edge for use in a {@link Graph}.
 *
 * @author Arne Keller
 */
public interface GraphEdge<V> {
    /**
     * @return where this edge starts
     */
    V getSource();

    /**
     * @return where this edge goes to
     */
    V getTarget();

    /**
     * Specify the source of this edge.
     *
     * @param source source node
     */
    void setSource(V source);

    /**
     * Specify the target of this edge.
     *
     * @param target target node
     */
    void setTarget(V target);
}

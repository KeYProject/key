package org.key_project.util.collection;

/**
 * Graph edge for use in a {@link Graph}.
 */
public interface GraphEdge {
    Object getSource();
    Object getTarget();

    void setSource(Object source);
    void setTarget(Object target);
}

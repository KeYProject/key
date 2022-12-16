package org.key_project.util.collection;

/**
 * Directed graph edge for use in {@link DirectedGraph}.
 */
public class DefaultEdge implements GraphEdge {
    private Object source;
    private Object target;

    @Override
    public Object getSource() {
        return source;
    }

    @Override
    public void setSource(Object source) {
        this.source = source;
    }

    @Override
    public Object getTarget() {
        return target;
    }

    @Override
    public void setTarget(Object target) {
        this.target = target;
    }
}

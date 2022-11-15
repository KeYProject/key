package de.uka.ilkd.key.proof.io.intermediate;

import java.util.ArrayDeque;
import java.util.LinkedList;
import java.util.List;
import java.util.function.Consumer;

/**
 * Node in an intermediate proof representation. Responsible for storing information about children
 * of nodes.
 *
 * @author Dominic Scheurer
 */
public abstract class NodeIntermediate {

    private LinkedList<NodeIntermediate> children = new LinkedList<>();
    /**
     * Number of nodes in the node tree rooted at this object.
     * Cached value, computed on first request.
     */
    private int subtreeSize = -1;

    public LinkedList<NodeIntermediate> getChildren() {
        return children;
    }

    public void setChildren(LinkedList<NodeIntermediate> children) {
        this.children = children;
        this.subtreeSize = -1;
    }

    public void addChild(NodeIntermediate child) {
        this.children.add(child);
        this.subtreeSize = -1;
    }

    public int subtreeSize() {
        if (subtreeSize != -1) {
            return subtreeSize;
        }
        var total = 1;
        var queue = new ArrayDeque<>(getChildren());
        while (!queue.isEmpty()) {
            total++;
            queue.addAll(queue.pollFirst().getChildren());
        }
        subtreeSize = total;
        return total;
    }

    /**
     * Visit this object and all children nodes in a depth-first order.
     *
     * @param visitor callback to accept node objects
     */
    public void depthFirstVisit(Consumer<NodeIntermediate> visitor) {
        var queue = new ArrayDeque<>(List.of(this));
        while (!queue.isEmpty()) {
            var node = queue.pollFirst();
            visitor.accept(node);
            node.children.descendingIterator().forEachRemaining(queue::addFirst);
        }
    }
}

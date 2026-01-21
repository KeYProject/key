package de.uka.ilkd.key.proof.io.intermediate;

import java.util.ArrayDeque;
import java.util.LinkedList;

/**
 * Node in an intermediate proof representation. Responsible for storing information about children
 * of nodes.
 *
 * @author Dominic Scheurer
 */
public abstract class NodeIntermediate {

    private LinkedList<NodeIntermediate> children = new LinkedList<NodeIntermediate>();

    public LinkedList<NodeIntermediate> getChildren() {
        return children;
    }

    public void setChildren(LinkedList<NodeIntermediate> children) {
        this.children = children;
    }

    public void addChild(NodeIntermediate child) {
        this.children.add(child);
    }

    /**
     * @return number of NodeIntermediates in this tree of nodes (including this node)
     */
    public int countAllChildren() {
        var total = 1;
        var queue = new ArrayDeque<>(getChildren());
        while (!queue.isEmpty()) {
            total++;
            queue.addAll(queue.pollFirst().getChildren());
        }
        return total;
    }
}

package de.uka.ilkd.key.util.script;

import java.io.Serializable;
import java.util.*;

import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;

/**
 * @author Alexander Weigl
 * @version 1 (06.12.18)
 */
public class NodeIdentifier implements Serializable {
    List<Integer> list = new ArrayList<>();

    public NodeIdentifier() {
    }

    public NodeIdentifier(List<Integer> seq) {
        this.list.addAll(list);
    }

    public void setList(List<Integer> list) {
        this.list = list;
    }

    public List<Integer> getList() {
        return list;
    }

    public static NodeIdentifier get(Node node) {
        final LinkedList<Integer> list = new LinkedList<>();
        do {
            Node parent = node.parent();
            if (parent != null) {
                list.add(0, parent.getChildNr(node));
            }
            node = parent;
        } while (node != null);
        return new NodeIdentifier(list);
    }

    public Optional<Node> findNode(Proof proof) {
        return findNode(proof.root());
    }

    public Optional<Node> findNode(Node node) {
        for (int child : list) {
            if (child <= node.childrenCount()) {
                node = node.child(child);
            } else {
                return Optional.empty();
            }
        }
        return Optional.of(node);
    }
}

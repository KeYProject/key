package de.uka.ilkd.key.gui.interactionlog;

import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;

import java.io.Serializable;
import java.util.*;

/**
 * @author Alexander Weigl
 * @version 1 (06.12.18)
 */
public class NodeIdentifier implements Serializable {
    final ArrayList<Integer> list = new ArrayList<>();

    public NodeIdentifier(LinkedList<Integer> seq) {
        this.list.addAll(list);
    }

    public Collection<Integer> get() {
        return Collections.unmodifiableCollection(list);
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

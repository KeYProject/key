package de.uka.ilkd.key.util.script;

import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;

import java.util.*;
import java.util.stream.Collectors;

/**
 * depcrated in favor interaction log
 *
 * @author weigl
 */
@Deprecated
public final class ScriptRecorderState {
    private final Proof proof;
    private List<Interaction> interactions = new LinkedList<>();

    public ScriptRecorderState(Proof proof) {
        this.proof = proof;
    }

    public List<Interaction> getInteractions() {
        return interactions;
    }


    public Proof getProof() {

        return proof;
    }

    public List<List<NodeInteraction>> getInteractionsByDepth() {
        final Map<Integer, List<Interaction>> seq = new HashMap<>();
        int maxDepth = 0;
        for (Interaction event : interactions) {
            if (event instanceof NodeInteraction) {
                int depth = getDepth(((NodeInteraction) event).getNode());
                maxDepth = Math.max(maxDepth, depth);
                seq.computeIfAbsent(depth, n -> new ArrayList<>()).add(event);
            }
        }
        for (int d = 0; d < maxDepth; d++) {

        }
        return null;
    }

    private int getDepth(Node n) {
        int d = 0;
        while (n.parent() != null) {
            n = n.parent();
            d++;
        }
        return d;
    }

    public HashMap<Interaction, List<Interaction>> getInteractionTree() {
        final HashMap<Interaction, List<Interaction>> map = new HashMap<>();
        final Set<Node> interactiveNodes = interactions.stream()
                .filter(e -> e instanceof NodeInteraction)
                .map(e -> (NodeInteraction) e)
                .map(NodeInteraction::getNode)
                .collect(Collectors.toSet());


        for (Interaction inter : interactions) {
            if (inter instanceof NodeInteraction) {
                NodeInteraction parent = findNearestAncestor(interactiveNodes,
                        ((NodeInteraction) inter).getNode());
                map.computeIfAbsent(parent, n -> new ArrayList<>()).add(inter);
            }
        }

        return map;
    }

    private NodeInteraction findNearestAncestor(Set<Node> parents, Node n) {
        do {
            n = n.parent();
            if (n == null) break;
            if (parents.contains(n)) {
                Node finalN = n;
                return interactions.stream()
                        .filter(e -> e instanceof NodeInteraction)
                        .map(e -> (NodeInteraction) e)
                        .filter((NodeInteraction a) -> a.getNode().serialNr() == finalN.serialNr())
                        .findFirst()
                        .orElse(null);
            }
        } while (true);
        return null;
    }
}

package de.uka.ilkd.key.util.script;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.macros.ProofMacro;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.TacletApp;
import org.key_project.util.collection.ImmutableList;

import java.util.*;
import java.util.stream.Collectors;

/**
 * @author weigl
 */
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

    public List<List<Interaction>> getInteractionsByDepth() {
        final Map<Integer, List<Interaction>> seq = new HashMap<>();
        int maxDepth = 0;
        for (Interaction event : interactions) {
            int depth = getDepth(event.getNode());
            maxDepth = Math.max(maxDepth, depth);
            seq.computeIfAbsent(depth, n -> new ArrayList<>()).add(event);
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
        final Set<Node> interactiveNodes = interactions.stream().map(
                Interaction::getNode).collect(Collectors.toSet());

        for (Interaction inter : interactions) {
            Interaction parent = findNearestAncestor(interactiveNodes, inter.getNode());
            map.computeIfAbsent(parent, n -> new ArrayList<>()).add(inter);
        }

        return map;
    }

    private Interaction findNearestAncestor(Set<Node> parents, Node n) {
        do {
            n = n.parent();
            if (n == null) break;
            if (parents.contains(n)) {
                Node finalN = n;
                return interactions.stream()
                        .filter((Interaction a) -> a.getNode().serialNr() == finalN.serialNr())
                        .findFirst()
                        .orElse(null);
            }
        } while (true);
        return null;
    }
}

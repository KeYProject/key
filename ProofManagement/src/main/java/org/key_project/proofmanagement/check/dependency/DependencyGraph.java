package org.key_project.proofmanagement.check.dependency;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

public class DependencyGraph {

    private final Map<DependencyNode, DependencyNode> nodes = new HashMap<>();

    public void addNode(DependencyNode node) {
        nodes.put(node, node);
    }

    public Map<DependencyNode, DependencyNode> getNodes() {
        return nodes;
    }

    public boolean isLegal() {
        for(DependencyNode currentNode : nodes.keySet()) {
            if(!currentNode.isLegal()) {
                return false;
            }
        }
        return true;
    }

    @Override
    public String toString() {
        String result = "";
        for(DependencyNode currentNode : nodes.keySet()) {
            result = result + currentNode + "\n";
        }
        return result;
    }

}

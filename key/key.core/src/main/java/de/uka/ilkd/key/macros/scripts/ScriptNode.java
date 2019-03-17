package de.uka.ilkd.key.macros.scripts;

import de.uka.ilkd.key.proof.Node;

import java.util.LinkedList;
import java.util.List;
import java.util.Map;

public class ScriptNode {
    
    private Map<String, String> command;
    private int fromPos;
    private int toPos;
    private ScriptNode parent;
    private List<ScriptNode> children = new LinkedList<>();
    private Node proofNode;
    private Throwable encounteredException;

    public ScriptNode(ScriptNode parent, Map<String, String> command, int fromPos, int toPos) {
        this.parent = parent;
        this.command = command;
        this.fromPos = fromPos;
        this.toPos = toPos;
    }

    public void addNode(ScriptNode node) {
        children.add(node);
    }
    
    public void dump(int indent) {
        for (int i = 0; i < indent; i++) {
            System.out.print(" ");
        }
        System.out.print(proofNode == null ? "xxx" : proofNode.serialNr() );
        System.out.println(" " + command);
        for (ScriptNode child : children) {
            child.dump(indent + 1);
        }
    }

    public Map<String, String> getCommand() {
        return command;
    }

    public Node getProofNode() {
        return proofNode;
    }

    public void setProofNode(Node proofNode) {
        this.proofNode = proofNode;
    }

    public List<ScriptNode> getChildren() {
        return children;
    }

    public int getFromPos() {
        return fromPos;
    }

    public int getToPos() {
        return toPos;
    }
    
    public void clearChildren() {
        children.clear();
    }

    public Throwable getEncounteredException() {
        return encounteredException;
    }

    public void setEncounteredException(Throwable encounteredException) {
        this.encounteredException = encounteredException;
    }
    public ScriptNode getParent(){
        return parent;
    }
    public boolean isRoot(){
        return (parent == null);
    }


}


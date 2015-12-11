package de.uka.ilkd.key.prooftree;

import java.util.LinkedList;

public class BranchNode extends Node {

    private de.uka.ilkd.key.proof.Node firstChild;
    
    private LinkedList<Node> children;
    
    /**
     * @param firstChild
     */
    public BranchNode(de.uka.ilkd.key.proof.Node firstChild) {
        this.firstChild = firstChild;
        children = new LinkedList<Node>();
    }

    /**
     * @return the firstChild
     */
    public de.uka.ilkd.key.proof.Node getFirstChild() {
        return firstChild;
    }

    /**
     * @param firstChild the firstChild to set
     */
    public void setFirstChild(de.uka.ilkd.key.proof.Node firstChild) {
        this.firstChild = firstChild;
    }

    /**
     * @return the children
     */
    public LinkedList<Node> getChildren() {
        return children;
    }

    /**
     * @param children the children to set
     */
    public void setChildren(LinkedList<Node> children) {
        this.children = children;
    }
    
    /**
     * @param children the children to set
     */
    public void addChild(Node child) {
        this.children.addLast(child);
    }
}

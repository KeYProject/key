package de.uka.ilkd.key.nui.prooftree;

import java.util.LinkedList;

public class NUIBranchNode extends NUINode {

    private de.uka.ilkd.key.proof.Node parent;
    
    private LinkedList<NUINode> children;
    
    /**
     * @param parent
     */
    public NUIBranchNode(de.uka.ilkd.key.proof.Node parent) {
        this.parent = parent;
        children = new LinkedList<NUINode>();
    }

    /**
     * @return the firstChild
     */
    public de.uka.ilkd.key.proof.Node getFirstChild() {
        return parent;
    }

    /**
     * @param firstChild the firstChild to set
     */
    public void setFirstChild(de.uka.ilkd.key.proof.Node firstChild) {
        this.parent = firstChild;
    }

    /**
     * @return the children
     */
    public LinkedList<NUINode> getChildren() {
        return children;
    }

    /**
     * @param children the children to set
     */
    public void setChildren(LinkedList<NUINode> children) {
        this.children = children;
    }
    
    /**
     * @param children the children to set
     */
    public void addChild(NUINode child) {
        this.children.addLast(child);
    }
}

package de.uka.ilkd.key.nui.prooftree;

import java.util.LinkedList;
import java.util.List;

/**
 * Represents a branch node. Is used to create a graphical representation of a
 * proof tree consisting of {@link de.uka.ilkd.key.proof.Node} objects.
 * 
 * @author Matthias Schultheis
 * @author Patrick Jattke
 *
 */
public class NUIBranchNode extends NUINode {

    /**
     * A list of children of the branch node.
     */
    private final List<NUINode> children = new LinkedList<>();

    /**
     * The parent node of the branch node.
     */
    private de.uka.ilkd.key.proof.Node proofParentNode;

    /**
     * Creates a new branch node.
     * 
     * @param proofParentNode
     *            The related parent node of the branch node.
     */
    public NUIBranchNode(final de.uka.ilkd.key.proof.Node proofParentNode) {
        super();
        this.proofParentNode = proofParentNode;

    }

    /**
     * Adds a new child to the list of children.
     * 
     * @param child
     *            The child to add.
     */
    public final void addChild(final NUINode child) {
        this.children.add(child);
    }
    
    @Override
    public List<NUINode> asList(){
        List<NUINode> l = new LinkedList<>();
        l.add(this);
        children.forEach((child) -> l.addAll(child.asList()));
        return l;
    }

    /**
     * Returns a list of children of the branch node.
     * 
     * @return children A LinkedList of the branch node's children.
     */
    public final List<NUINode> getChildren() {
        return children;
    }

    /**
     * Returns the parent node of the branch node.
     * 
     * @return parent The parent node of the branch node.
     */
    public final de.uka.ilkd.key.proof.Node getProofParentNode() {
        return proofParentNode;
    }

    /**
     * Checks if all branch node children are marked as linked.
     * 
     * @return true iff all branch node children are linked
     */
    public final boolean hasOnlyLinkedBranchChildren() {
        for (NUINode child : children) {
            if (child instanceof NUIBranchNode && !child.isLinked()) {
                return false;
            }
        }
        return true;
    }

    public void resetSearch() {
        setSearchResult(false);
        children.forEach((child) -> child.resetSearch());
    }

    @Override
    public boolean search(String term) {
        if(term.isEmpty()) return false;
        
        if (getLabel().toLowerCase().contains(term.toLowerCase())) {
            setSearchResult(true);
            children.forEach((child) -> child.search(term));
         //   System.out.println(this + " was searched for " + term + "and highlighted? " + true);
            return true;
        }
        else {
            setSearchResult(false);
            boolean returnvalue = false;
            for(NUINode n : children){
                if(n.search(term)) { returnvalue = true; }
            }
           // System.out.println(this + ", a BranchNode was searched for '" + term + "' and highlighted? " + returnvalue);
            return returnvalue;
        }
    }

    /**
     * Sets the parent node of the branch node.
     * 
     * @param parent
     *            The node to set as parent node of the branch node.
     */
    public final void setProofParentNode(final de.uka.ilkd.key.proof.Node parent) {
        this.proofParentNode = parent;
    }
}

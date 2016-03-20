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
    private List<NUINode> children = new LinkedList<>();

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

    /**
     * Returns a list of children of the branch node.
     * 
     * @return children A LinkedList of the branch node's children.
     */
    public final List<NUINode> getChildren() {
        return children;
    }

    /**
     * Sets the children of the branch node.
     * 
     * @param children
     *            The children to set for the branch node.
     */
    public void setChildren(final List<NUINode> children) {
        this.children = children;
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
        for (final NUINode child : children) {
            if (child instanceof NUIBranchNode && !child.isLinked()) {
                return false;
            }
        }
        return true;
    }

    @Override
    public void resetSearch() {
        setSearchResult(false);
        children.forEach((child) -> child.resetSearch());
    }

    @Override
    public int search(final String term) {
        // case: Empty search term given
        if (term.isEmpty()) {
            return 0;
        }

        // case: Non-Empty search term given

        final boolean thisIsASearchResult = getLabel().toLowerCase().contains(term.toLowerCase());

        setSearchResult(thisIsASearchResult);
        return children.stream()/*.parallel()*/.mapToInt((child) -> child.search(term)).sum()
                + (thisIsASearchResult ? 1 : 0);
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

    @Override
    public NUIBranchNode clone() throws CloneNotSupportedException {
        // create clone
        final NUIBranchNode cloned = new NUIBranchNode(proofParentNode);
        this.copyFields(this, cloned);

        // set children
        final LinkedList<NUINode> newChildren = new LinkedList<>();
        for (final NUINode child : this.children) {
            final NUINode clonedChild = child.clone();
            clonedChild.setParent(cloned);
            newChildren.add(clonedChild);
        }
        cloned.setChildren(newChildren);

        return cloned;
    }

    /**
     * Clones the branch node without children. The children list will be empty.
     * 
     * @return the cloned branch node
     */
    public NUIBranchNode cloneWithoutChildren() {
        // create clone
        final NUIBranchNode cloned = new NUIBranchNode(proofParentNode);
        this.copyFields(this, cloned);

        return cloned;
    }

    @Override
    public List<NUINode> asList() {

        final List<NUINode> list = new LinkedList<>();
        list.add(this);
        children.forEach((child) -> list.addAll(child.asList()));
        return list;

    }

}

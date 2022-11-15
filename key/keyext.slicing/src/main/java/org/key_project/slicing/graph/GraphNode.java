package org.key_project.slicing.graph;

import de.uka.ilkd.key.proof.BranchLocation;

/**
 * A graph node used in the {@link DependencyGraph}.
 *
 * @author Arne Keller
 */
public abstract class GraphNode {
    /**
     * Location in the proof tree.
     */
    protected final BranchLocation branchLocation;

    protected GraphNode(BranchLocation branchLocation) {
        this.branchLocation = branchLocation;
    }

    /**
     * @return the branch location of this node (empty if not applicable / necessary)
     */
    public BranchLocation getBranchLocation() {
        return branchLocation;
    }

    public abstract GraphNode popLastBranchID();

    /**
     * Construct a human-friendly representation of this graph node.
     *
     * @param abbreviated whether any text should be abbreviated
     * @param omitBranch do not include branch info
     * @return textual representation of this object
     */
    public abstract String toString(boolean abbreviated, boolean omitBranch);
}

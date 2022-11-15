package org.key_project.slicing.graph;

import de.uka.ilkd.key.proof.BranchLocation;

/**
 * Graph node representing an open goal.
 */
public class OpenGoal extends GraphNode {
    public OpenGoal(BranchLocation location) {
        super(location);
    }

    @Override
    public GraphNode popLastBranchID() {
        return new OpenGoal(super.getBranchLocation().removeLast());
    }

    @Override
    public String toString(boolean abbreviated, boolean omitBranch) {
        return omitBranch ? "OpenGoal{...}"
                : String.format("Opengoal{%s}", getBranchLocation().toString());
    }
}

package org.key_project.exploration;

/**
 * Information on exploration that is attached to nodes.
 * If such an object is attached to a node, this node will be highlighted in the tree with a border
 * and if an ExplorationAction is set this action is displayed in the ExplorationStepsList Tab
 */
public class ExplorationNodeData {

    private  String explorationAction;

    /**
     * Return the String of the Exploration action that was applied to the node
     * @return
     */
    public String getExplorationAction() {
        return explorationAction;
    }

    /**
     * Set the String of the Exploration action that was applied to the node
     * @param explorationAction
     */
    public void setExplorationAction(String explorationAction) {
        this.explorationAction = explorationAction;
    }
}

package org.key_project.exploration;

import de.uka.ilkd.key.proof.Node;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.Objects;

/**
 * Information on exploration that is attached to nodes.
 * If such an object is attached to a node, this node will be highlighted in the tree with a border
 * and if an ExplorationAction is set this action is displayed in the ExplorationStepsList Tab
 */
public class ExplorationNodeData {

    private  String explorationAction;

    public static @NotNull ExplorationNodeData get(@NotNull Node node) {
        @Nullable ExplorationNodeData data = node.lookup(ExplorationNodeData.class);
        if(data == null) {
            data = new ExplorationNodeData();
            node.register(data, ExplorationNodeData.class);
        }
        return data;
    }

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


    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (!(o instanceof ExplorationNodeData)) return false;
        ExplorationNodeData that = (ExplorationNodeData) o;
        return Objects.equals(getExplorationAction(), that.getExplorationAction());
    }

    @Override
    public int hashCode() {
        return Objects.hash(getExplorationAction());
    }
}

/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.exploration;

import de.uka.ilkd.key.proof.Node;
import org.jspecify.annotations.Nullable;

import java.util.Objects;

/**
 * Information on exploration that is attached to nodes. If such an object is attached to a node,
 * this node will be highlighted in the tree with a border and if an ExplorationAction is set this
 * action is displayed in the ExplorationStepsList Tab
 */
public class ExplorationNodeData {
    private @Nullable String explorationAction;

    public static ExplorationNodeData get(Node node) {
        ExplorationNodeData data = node.lookup(ExplorationNodeData.class);
        if (data == null) {
            data = new ExplorationNodeData();
            node.register(data, ExplorationNodeData.class);
        }
        return data;
    }

    /**
     * Return the String of the Exploration action that was applied to the node
     */
    public @Nullable String getExplorationAction() {
        return explorationAction;
    }

    /**
     * Set the String of the Exploration action that was applied to the node
     */
    public void setExplorationAction(String explorationAction) {
        this.explorationAction = explorationAction;
    }


    @Override
    public boolean equals(@Nullable Object o) {
        if (this == o) {
            return true;
        }
        if (o == null) {
            return false;
        }
        if (o.getClass() != getClass()) {
            return false;
        }
        ExplorationNodeData that = (ExplorationNodeData) o;
        return Objects.equals(getExplorationAction(), that.getExplorationAction());
    }

    @Override
    public int hashCode() {
        return Objects.hash(getExplorationAction());
    }
}

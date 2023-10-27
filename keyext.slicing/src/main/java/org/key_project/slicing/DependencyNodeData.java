/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.slicing;

import java.util.Collections;
import java.util.List;

import de.uka.ilkd.key.util.Pair;

import org.key_project.slicing.graph.GraphNode;

/**
 * Stores the dependency graph nodes touched by a proof step.
 * Added to a node using {@link de.uka.ilkd.key.proof.Node#register(Object, Class)}.
 *
 * @author Arne Keller
 */
public class DependencyNodeData {
    /**
     * List of graph nodes required to instantiate the proof step. Each boolean indicates whether
     * the graph node was replaced (consumed) by this proof step.
     */
    public final List<Pair<GraphNode, Boolean>> inputs;
    /**
     * New graph nodes (formulas, ..) introduced by this proof step.
     */
    public final List<GraphNode> outputs;
    /**
     * Label for this proof step.
     */
    public final String label;

    /**
     * Construct a new container for dependency node data.
     *
     * @param inputs graph nodes used by the proof step
     * @param outputs graph nodes created by the proof step
     * @param label label for this node
     */
    public DependencyNodeData(List<Pair<GraphNode, Boolean>> inputs, List<GraphNode> outputs,
            String label) {
        this.inputs = Collections.unmodifiableList(inputs);
        this.outputs = Collections.unmodifiableList(outputs);
        this.label = label;
    }
}

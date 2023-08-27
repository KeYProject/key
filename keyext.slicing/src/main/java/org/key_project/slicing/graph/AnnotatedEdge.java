/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.slicing.graph;

import de.uka.ilkd.key.proof.Node;

import org.key_project.util.collection.DefaultEdge;

/**
 * An edge of the dependency graph. Stores additional metadata.
 *
 * @author Arne Keller
 */
public class AnnotatedEdge extends DefaultEdge {
    /**
     * The node that added this edge to the dependency graph.
     */
    private final Node proofStep;
    /**
     * Whether the proof step consumes (replaces) the input formula.
     */
    private final boolean consumesInput;

    /**
     * Construct a new annotated edge.
     *
     * @param proofStep proof step
     * @param consumesInput whether the step replaced the input formula
     */
    public AnnotatedEdge(Node proofStep, boolean consumesInput) {
        this.proofStep = proofStep;
        this.consumesInput = consumesInput;
    }

    /**
     * @return tte node that added this edge to the dependency graph
     */
    public Node getProofStep() {
        return proofStep;
    }

    /**
     * @return whether the proof step consumes (replaces) the input formula
     */
    public boolean replacesInputNode() {
        return consumesInput;
    }
}

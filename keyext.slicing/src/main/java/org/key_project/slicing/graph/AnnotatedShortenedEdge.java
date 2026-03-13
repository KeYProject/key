/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.slicing.graph;

import de.uka.ilkd.key.proof.Node;

import org.key_project.prover.rules.RuleApp;

/**
 * An annotated edge representing a chain of real proof nodes.
 *
 * @author Arne Keller
 */
public class AnnotatedShortenedEdge extends AnnotatedEdge {
    /**
     * The initial node in this shortened chain.
     */
    private final Node initial;
    /**
     * The last node in this shortened chain.
     */
    private final Node last;

    /**
     * Create a new shortened edge.
     *
     * @param initial the initial node for this shortened chain
     * @param last the last node of this shortened chain
     * @param consumesInput whether the input graph node is consumed
     */
    public AnnotatedShortenedEdge(Node initial, Node last, boolean consumesInput) {
        super(last, consumesInput);
        this.initial = initial;
        this.last = last;
    }

    /**
     * Get the proper label for this edge.
     * Will list both the initial and the last node's ruleapp.
     *
     * @return label for this edge (to use in DOT export)
     */
    public String getEdgeLabel() {
        var sb = new StringBuilder();
        RuleApp ruleApp1 = initial.getAppliedRuleApp();
        if (ruleApp1 != null) {
            sb.append(ruleApp1.rule().displayName()).append("_").append(initial.serialNr());
            sb.append(" ... ");
        }
        RuleApp ruleApp2 = last.getAppliedRuleApp();
        if (ruleApp2 != null) {
            sb.append(ruleApp2.rule().displayName()).append("_").append(last.serialNr());
        }
        return sb.toString();
    }

    public Node getInitial() {
        return initial;
    }
}

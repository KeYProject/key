/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.proofevent;


import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.RuleApp;

import org.key_project.util.collection.ImmutableList;

/**
 * More specific information about a rule application: the original proof node and the new proof
 * node(s) created by this rule application.
 */
public class RuleAppInfo {

    /**
     * RuleApp this event reports
     */
    private final RuleApp app;

    /**
     * Node the rule has been applied on
     */
    private final Node originalNode;

    /**
     * New nodes that have been introduced by this rule application
     */
    private final ImmutableList<NodeReplacement> newNodes;

    /**
     * Construct a new rule application information container.
     *
     * @param appliedRule the applied rule
     * @param originalNode node the rule was applied on
     * @param newNodes node(s) created by the rule application
     */
    RuleAppInfo(RuleApp appliedRule, Node originalNode,
            ImmutableList<NodeReplacement> newNodes) {
        this.app = appliedRule;
        this.originalNode = originalNode;
        this.newNodes = newNodes;
    }

    public RuleApp getRuleApp() {
        return app;
    }

    /**
     * @return Node the rule has been applied on
     */
    public Node getOriginalNode() {
        return originalNode;
    }

    /**
     * @return Nodes by which the original one has been replaced (the original node, if only the
     *         closure constraint of this node has been changed)
     */
    public ImmutableList<NodeReplacement> getReplacementNodes() {
        return newNodes;
    }


    public String toString() {
        return "RuleApp: " + getRuleApp() + "\nNode: " + getOriginalNode() + "\nResulting nodes: "
            + newNodes;
    }
}

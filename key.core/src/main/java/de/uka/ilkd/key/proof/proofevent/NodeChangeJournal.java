/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.proofevent;


import java.util.Iterator;

import de.uka.ilkd.key.logic.SequentChangeInfo;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.GoalListener;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.RuleApp;

import org.key_project.util.collection.DefaultImmutableMap;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableMap;
import org.key_project.util.collection.ImmutableMapEntry;
import org.key_project.util.collection.ImmutableSLList;


/**
 * Collect changes applied to a node during a given period of time
 */
public class NodeChangeJournal implements GoalListener {

    private final Proof proof;

    /**
     * The original node
     */
    private final Node node;

    /**
     * This is a may storing the leaves that are currently below the original node, and all changes
     * applied to each of them
     */
    private ImmutableMap<Node, NodeChangesHolder> changes =
        DefaultImmutableMap.nilMap();

    /**
     * @param p_goal the original goal/node
     */
    public NodeChangeJournal(Proof p_proof, Goal p_goal) {
        proof = p_proof;
        node = p_goal.node();
        putChangeObj(node, new NodeChangesHolder());
    }


    /**
     * Create an RuleAppInfo object containing all changes stored within this object; remove all
     * listeners
     */
    public RuleAppInfo getRuleAppInfo(RuleApp p_ruleApp) {
        ImmutableList<NodeReplacement> nrs = ImmutableSLList.nil();

        for (final ImmutableMapEntry<Node, NodeChangesHolder> entry : changes) {
            final Node newNode = entry.key();
            final Goal newGoal = proof.getOpenGoal(newNode);

            if (newGoal != null) {
                final NodeChangesHolder nc = entry.value();

                nrs = nrs.prepend(new NodeReplacement(newNode, node, nc.scis));

                newGoal.removeGoalListener(this);
            }
        }

        return new RuleAppInfo(p_ruleApp, node, nrs);
    }


    // GoalListener methods

    /**
     * informs the listener about a change that occured to the sequent of goal
     */
    public void sequentChanged(Goal source, SequentChangeInfo sci) {
        NodeChangesHolder nc = getChangeObj(source.node());

        if (nc != null) {
            nc.addSCI(sci);
        }
    }


    /**
     * Informs the listener that the given goal <code>source</code> has been replaced by the goals
     * <code>newGoals</code> (note that <code>source</code> may be an element of
     * <code>newGoals</code>). The nodes of <code>newGoals</code> are children of the node
     * <code>parent</code>
     */
    public void goalReplaced(Goal source, Node parent, ImmutableList<Goal> newGoals) {
        NodeChangesHolder nc = removeChangeObj(parent);

        if (nc != null) {
            Iterator<Goal> it = newGoals.iterator();
            if (it.hasNext()) {
                while (true) {
                    putChangeObj(it.next().node(), nc);
                    if (!it.hasNext()) {
                        break;
                    }
                    nc = (NodeChangesHolder) nc.clone();
                }
            }
        }
    }


    private void putChangeObj(Node p_node, NodeChangesHolder p_obj) {
        changes = changes.put(p_node, p_obj);
    }

    private NodeChangesHolder getChangeObj(Node p_node) {
        return changes.get(p_node);
    }

    private NodeChangesHolder removeChangeObj(Node p_node) {
        final NodeChangesHolder res = changes.get(p_node);
        changes = changes.remove(p_node);
        return res;
    }

    @Override
    public void automaticStateChanged(Goal source, boolean oldAutomatic, boolean newAutomatic) {
        // Nothing to do
    }
}

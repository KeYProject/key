/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof;

import java.util.*;
import javax.swing.*;

import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.merge.MergePartner;
import de.uka.ilkd.key.rule.merge.MergeRuleBuiltInRuleApp;
import de.uka.ilkd.key.settings.GeneralSettings;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

/**
 * This class is responsible for pruning a proof tree at a certain cutting point. It has been
 * introduced to encapsulate the methods that are needed for pruning. Since the class has
 * influence on the internal state of the proof it should not be moved to a new file, in order
 * to restrict the access to it.
 */
class ProofPruner {
    private final Proof proof;
    private Node firstLeaf = null;

    ProofPruner(Proof proof) {
        this.proof = proof;
    }

    /**
     * prunes the proof at the given node
     *
     * @param cuttingPoint the node where to prune
     * @return the subtrees whose common root was the given {@code cuttingPoint}
     */
    public ImmutableList<Node> prune(final Node cuttingPoint) {

        // there is only one leaf containing an open goal that is interesting for pruning the
        // subtree of <code>node</code>, namely the first leave that is found by a breadth
        // first search.
        // The other leaves containing open goals are only important for removing the open goals
        // from the open goal list.
        // To that end, those leaves are stored in residualLeaves. For increasing the
        // performance,
        // a tree structure has been chosen, because it offers the operation
        // <code>contains</code> in O(log n).
        final Set<Node> residualLeaves = new TreeSet<>(Comparator.comparingInt(Node::serialNr));

        final InitConfig initConfig = proof.getInitConfig();

        // First, make a breadth first search, in order to find the leaf
        // with the shortest distance to the cutting point and to remove
        // the rule applications from the proof management system.
        // Furthermore, store the residual leaves.
        proof.breadthFirstSearch(cuttingPoint, (proof, visitedNode) -> {
            if (visitedNode.leaf()) {
                // pruning in closed branches (can be disabled via "--no-pruning-closed")
                if (!visitedNode.isClosed() || !GeneralSettings.noPruningClosed) {
                    if (firstLeaf == null) {
                        firstLeaf = visitedNode;
                    } else {
                        residualLeaves.add(visitedNode);
                    }
                }
            }

            if (initConfig != null && visitedNode.parent() != null) {
                proof.getServices().getDepRepo().ruleUnApplied(visitedNode.parent().getAppliedRuleApp(), proof);
                for (final NoPosTacletApp app : visitedNode.parent()
                        .getLocalIntroducedRules()) {
                    initConfig.getJustifInfo().removeJustificationFor(app.taclet());
                }
            }

            // Merge rule applications: Unlink all merge partners.
            if (visitedNode.getAppliedRuleApp() instanceof MergeRuleBuiltInRuleApp mergeApp) {

                for (MergePartner mergePartner : mergeApp.getMergePartners()) {
                    final Goal linkedGoal = mergePartner.getGoal();

                    if (linkedGoal.node().isClosed()) {
                        // The partner node has already been closed; we
                        // have to add the goal again.
                        proof.reOpenGoal(linkedGoal);
                    }

                    linkedGoal.setLinkedGoal(null);
                    SwingUtilities.invokeLater(() -> proof.pruneProof(linkedGoal));
                }
            }
        });

        // first leaf is closed -> add as goal and reopen
        final Goal firstGoal =
            firstLeaf.isClosed() ? proof.getClosedGoal(firstLeaf) : proof.getOpenGoal(firstLeaf);
        assert firstGoal != null;
        if (firstLeaf.isClosed()) {
            proof.reOpenGoal(firstGoal);
        }

        // TODO: WP: test interplay with merge rules
        // Cutting a linked goal (linked by a "defocusing" merge
        // operation, see {@link MergeRule}) unlinks this goal again.
        if (firstGoal.isLinked()) {
            firstGoal.setLinkedGoal(null);
        }

        // Go from the first leaf that has been found to the cutting point. For each node on the
        // path,
        // remove the local rules from firstGoal that have been added by the considered node.
        proof.traverseFromChildToParent(firstLeaf, cuttingPoint, (proof, visitedNode) -> {
            for (final NoPosTacletApp app : visitedNode.getLocalIntroducedRules()) {
                firstGoal.ruleAppIndex().removeNoPosTacletApp(app);
                proof.getInitConfig().getJustifInfo().removeJustificationFor(app.taclet());
            }

            firstGoal.pruneToParent();

            final List<StrategyInfoUndoMethod> undoMethods =
                visitedNode.getStrategyInfoUndoMethods();
            for (StrategyInfoUndoMethod undoMethod : undoMethods) {
                firstGoal.undoStrategyInfoAdd(undoMethod);
            }
        });


        // do some cleaning and refreshing: Clearing indices, caches....
        refreshGoal(firstGoal, cuttingPoint);

        // cut the subtree, it is not needed anymore.
        ImmutableList<Node> subtrees = cut(cuttingPoint);


        // remove the goals of the residual leaves.
        proof.removeOpenGoals(residualLeaves);
        proof.removeClosedGoals(residualLeaves);

        /*
         * this ensures that the open goals are in interactive mode and thus all rules are
         * available in the just pruned goal (see GitLab #1480)
         */
        proof.setRuleAppIndexToInteractiveMode();

        return subtrees;
    }

    private void refreshGoal(Goal goal, Node node) {
        goal.getRuleAppManager().clearCache();
        goal.ruleAppIndex().clearIndexes();
        goal.node().setAppliedRuleApp(null);
        node.clearNameCache();

        // delete NodeInfo, but preserve potentially existing branch label
        String branchLabel = node.getNodeInfo().getBranchLabel();
        node.clearNodeInfo();
        if (branchLabel != null) {
            node.getNodeInfo().setBranchLabel(branchLabel);
        }
    }

    private ImmutableList<Node> cut(Node node) {
        ImmutableList<Node> children = ImmutableSLList.nil();
        Iterator<Node> it = node.childrenIterator();

        while (it.hasNext()) {
            children = children.append(it.next());

        }
        for (Node child : children) {
            node.remove(child);
        }
        return children;
    }

}

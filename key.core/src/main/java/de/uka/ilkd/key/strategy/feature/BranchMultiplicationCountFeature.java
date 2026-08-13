/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.TacletApp;

import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.feature.Feature;
import org.key_project.util.Properties;

/**
 * Counts how often a rule has already been applied on the branch leading to a goal, and admits a
 * further application only while that count stays within a limit.
 *
 * <p>
 * The count is carried in the goal's strategy information rather than recomputed or held in a map.
 * A goal inherits the count of the node it grew from, so advancing costs one comparison, and
 * pruning restores the previous value through the undo method. A map keyed by node would instead
 * keep an entry for every node the proof ever had, which matters because macros such as the auto
 * pilot prune heavily.
 * </p>
 */
public final class BranchMultiplicationCountFeature extends BinaryTacletAppFeature {

    /**
     * The count as computed for one node. The serial number records which node that was, so a goal
     * that has since advanced can account for the steps in between. Serial numbers are used rather
     * than the nodes themselves so that nothing here keeps a pruned node, and with it a sequent,
     * reachable.
     *
     * @param nodeSerial the node the count was computed for
     * @param count applications carried by the branch strictly above that node
     */
    private record BranchCount(int nodeSerial, int count) {
    }

    private static final Properties.Property<BranchCount> COUNT_ON_BRANCH =
        new Properties.Property<>(BranchCount.class, "crossMultiplicationsOnBranch");


    private final String rulePrefix;
    private final int maxOnBranch;

    /**
     * Zero iff the branch leading to this goal carries at most {@code maxOnBranch} applications of
     * a rule whose name starts with {@code rulePrefix}.
     *
     * @param rulePrefix the name prefix identifying the rules to count
     * @param maxOnBranch the largest admitted number of earlier applications
     * @return the feature
     */
    public static Feature atMost(String rulePrefix, int maxOnBranch) {
        return new BranchMultiplicationCountFeature(rulePrefix, maxOnBranch);
    }

    private BranchMultiplicationCountFeature(String rulePrefix, int maxOnBranch) {
        this.rulePrefix = rulePrefix;
        this.maxOnBranch = maxOnBranch;
    }

    private boolean appliedHere(Node node) {
        final var applied = node.getAppliedRuleApp();
        return applied != null && applied.rule().name().toString().startsWith(rulePrefix);
    }

    /**
     * The applications carried by the branch strictly above the goal's node. Only the rules its
     * proper ancestors applied are counted: a goal has not applied one yet, so counting the node
     * itself would give a number every later goal on the branch inherits as one too small.
     */
    private int countFor(Goal goal) {
        final Node node = goal.node();
        final BranchCount known = goal.getStrategyInfo(COUNT_ON_BRANCH);
        if (known != null && known.nodeSerial() == node.serialNr()) {
            return known.count();
        }

        // Walk back to the node the inherited count belongs to, or to the root when there is none
        // to build on. That is one step in the common case, a goal having advanced by one node.
        int since = 0;
        Node walk = node;
        while (walk != null && (known == null || walk.serialNr() != known.nodeSerial())) {
            final Node parent = walk.parent();
            if (parent != null && appliedHere(parent)) {
                since++;
            }
            walk = parent;
        }
        // Reaching the root without meeting the remembered node means the count cannot be built on
        // it, and the walk has already counted the whole branch.
        final int total = (walk == null ? 0 : known.count()) + since;

        goal.addStrategyInfo(COUNT_ON_BRANCH, new BranchCount(node.serialNr(), total),
            strategyInfos -> strategyInfos.put(COUNT_ON_BRANCH, known));
        return total;
    }

    @Override
    protected boolean filter(TacletApp app, PosInOccurrence pos, Goal goal, MutableState mState) {
        return countFor(goal) <= maxOnBranch;
    }
}

/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.reference;

import java.util.ArrayList;
import java.util.List;
import java.util.function.Consumer;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.io.IntermediateProofReplayer;
import de.uka.ilkd.key.proof.replay.CopyingProofReplayer;

public class CopyReferenceResolver {
    /**
     * For each branch closed by reference to another proof,
     * copy the relevant proof steps into this proof.
     *
     * @param toComplete the proof whose references to closed branched shall be resolved by
     *        copying the branches
     * @param referencedFrom filter, if not null copy only from that proof
     * @param callbackTotal callback that gets the total number of branches to complete
     * @param callbackBranch callback notified every time a branch has been copied
     */
    public static void copyCachedGoals(
            Proof toComplete,
            Proof referencedFrom,
            Consumer<Integer> callbackTotal,
            Runnable callbackBranch) {
        // first, ensure that all cached goals are copied over
        List<Goal> goals = toComplete.closedGoals().toList();
        List<Goal> todo = new ArrayList<>();
        for (Goal g : goals) {
            Node node = g.node();
            ClosedBy c = node.lookup(ClosedBy.class);
            if (c == null) {
                continue;
            }
            if (referencedFrom != null && referencedFrom != c.proof()) {
                continue;
            }
            todo.add(g);
        }
        if (callbackTotal != null) {
            callbackTotal.accept(todo.size());
        }
        for (Goal g : todo) {
            toComplete.reOpenGoal(g);
            ClosedBy c = g.node().lookup(ClosedBy.class);
            g.node().deregister(c, ClosedBy.class);
            try {
                new CopyingProofReplayer(c.proof(), toComplete).copy(c.node(), g, c.nodesToSkip());
            } catch (IntermediateProofReplayer.BuiltInConstructionException e) {
                throw new RuntimeException(e);
            }
            if (callbackBranch != null) {
                callbackBranch.run();
            }
        }
    }
}

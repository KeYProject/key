/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.plugins.caching;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofTreeEvent;
import de.uka.ilkd.key.proof.ProofTreeListener;
import de.uka.ilkd.key.proof.reference.ClosedBy;

/**
 * Handles prunes in proofs that are referenced elsewhere.
 * If the branch that is pruned away is used as caching target (via {@link ClosedBy})
 * elsewhere, that reference is removed before the prune occurs.
 *
 * @author Arne Keller
 */
public class CachingPruneHandler implements ProofTreeListener {
    /**
     * The KeY mediator.
     */
    private final KeYMediator mediator;

    /**
     * Create a new handler.
     *
     * @param mediator the KeY mediator
     */
    public CachingPruneHandler(KeYMediator mediator) {
        this.mediator = mediator;
    }

    @Override
    public void proofIsBeingPruned(ProofTreeEvent e) {
        // check other proofs for any references to this proof
        for (Proof p : mediator.getCurrentlyOpenedProofs()) {
            for (Goal g : p.closedGoals()) {
                ClosedBy c = g.node().lookup(ClosedBy.class);
                if (c == null || c.proof() != e.getNode().proof()) {
                    continue;
                }
                var commonAncestor = e.getNode().commonAncestor(c.node());
                if (commonAncestor == c.node()) {
                    // proof is now open
                    // => remove caching reference
                    g.node().deregister(c, ClosedBy.class);
                    p.reOpenGoal(g);
                }
            }
        }
    }
}

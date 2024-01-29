/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.plugins.caching;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.IssueDialog;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.plugins.caching.settings.CachingSettingsProvider;
import de.uka.ilkd.key.gui.plugins.caching.settings.ProofCachingSettings;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofTreeEvent;
import de.uka.ilkd.key.proof.ProofTreeListener;
import de.uka.ilkd.key.proof.io.IntermediateProofReplayer;
import de.uka.ilkd.key.proof.reference.ClosedBy;
import de.uka.ilkd.key.proof.replay.CopyingProofReplayer;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Handles prunes in proofs that are referenced elsewhere.
 * If the branch that is pruned away is used as caching target (via {@link ClosedBy})
 * elsewhere, that reference is removed before the prune occurs.
 *
 * @author Arne Keller
 */
public class CachingPruneHandler implements ProofTreeListener {
    public static final Logger LOGGER = LoggerFactory.getLogger(CachingPruneHandler.class);

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
        Proof proofToBePruned = e.getSource();
        // check other proofs for any references to this proof
        for (Proof p : mediator.getCurrentlyOpenedProofs()) {
            for (Goal g : p.closedGoals()) {
                ClosedBy c = g.node().lookup(ClosedBy.class);
                if (c == null || c.proof() != proofToBePruned) {
                    continue;
                }
                var commonAncestor = e.getNode().commonAncestor(c.node());
                if (commonAncestor == c.node()) {
                    boolean copySteps = CachingSettingsProvider.getCachingSettings().getPrune()
                            .equals(ProofCachingSettings.PRUNE_COPY);
                    // proof is now open
                    // => remove caching reference
                    g.node().deregister(c, ClosedBy.class);
                    p.reOpenGoal(g);
                    if (copySteps) {
                        // quickly copy the proof before it is pruned
                        try {
                            new CopyingProofReplayer(c.proof(), p).copy(c.node(), g,
                                c.nodesToSkip());
                        } catch (IntermediateProofReplayer.BuiltInConstructionException ex) {
                            LOGGER.warn("failed to copy referenced proof that" +
                                "is about to be pruned", ex);
                            IssueDialog.showExceptionDialog(MainWindow.getInstance(), ex);
                        }
                    }
                }
            }
        }
    }
}

/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.plugins.caching.fx;

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
 * Handles prunes in proofs that are referenced elsewhere, FX port of {@code CachingPruneHandler}
 * (Swing CachingPruneHandler.java:30-80). If the branch that is pruned away is used as a caching
 * target (via {@link ClosedBy}) elsewhere, that reference is removed before the prune occurs and
 * — depending on the {@code ProofCachingSettings.prune} setting — the referenced steps are
 * copied into the caching proof.
 * <p>
 * <b>KNOWN-SIMPLIFIED:</b> the Swing original iterates {@code mediator.getCurrentlyOpenedProofs()}
 * (CachingPruneHandler.java:51); the FX port iterates the proofs tracked by the owning
 * {@link CachingExtensionF} instead (every proof selected at least once — the FX load path
 * selects each loaded proof, so this covers the currently opened proofs in practice). Proof
 * mutations triggered by a prune are engine operations and run on the caller (prover) thread,
 * like in Swing.
 *
 * @author Arne Keller (Swing original)
 * @author MP9.1 prune-handling port (FX)
 */
final class CachingPruneHandlerF implements ProofTreeListener {
    private static final Logger LOGGER = LoggerFactory.getLogger(CachingPruneHandlerF.class);

    /** the owning extension providing the tracked proofs */
    private final CachingExtensionF extension;

    /**
     * Create a new handler.
     *
     * @param extension the owning extension
     */
    CachingPruneHandlerF(CachingExtensionF extension) {
        this.extension = extension;
    }

    @Override
    public void proofIsBeingPruned(ProofTreeEvent event) {
        Proof proofToBePruned = event.getSource();
        // check other proofs for any references to this proof
        for (Proof p : extension.trackedProofsUnmodifiable()) {
            for (Goal g : p.closedGoals()) {
                ClosedBy c = g.node().lookup(ClosedBy.class);
                if (c == null || c.proof() != proofToBePruned) {
                    continue;
                }
                var commonAncestor = event.getNode().commonAncestor(c.node());
                if (commonAncestor == c.node()) {
                    boolean copySteps = CachingSettingsProviderF.getCachingSettings().getPrune()
                            .equals(ProofCachingSettings.PRUNE_COPY);
                    // proof is now open => remove caching reference
                    g.node().deregister(c, ClosedBy.class);
                    p.reOpenGoal(g);
                    if (copySteps) {
                        // quickly copy the proof before it is pruned
                        try {
                            new CopyingProofReplayer(c.proof(), p).copy(c.node(), g,
                                c.nodesToSkip());
                        } catch (IntermediateProofReplayer.BuiltInConstructionException ex) {
                            LOGGER.warn("failed to copy referenced proof that is about to be "
                                + "pruned", ex);
                        }
                    }
                }
            }
        }
    }
}

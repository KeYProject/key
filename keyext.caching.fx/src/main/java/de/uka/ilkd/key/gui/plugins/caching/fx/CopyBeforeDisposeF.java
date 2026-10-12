/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.plugins.caching.fx;

import de.uka.ilkd.key.core.fx.KeYMediatorF;
import de.uka.ilkd.key.gui.plugins.caching.settings.ProofCachingSettings;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.event.ProofDisposedEvent;
import de.uka.ilkd.key.proof.event.ProofDisposedListener;
import de.uka.ilkd.key.proof.reference.ClosedBy;
import de.uka.ilkd.key.proof.reference.CopyReferenceResolver;

import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * The listener ensuring that steps are copied before the referenced proof is disposed, FX port
 * of {@code CachingExtension.CopyBeforeDispose} (Swing CachingExtension.java:277-335). Registered
 * on the referenced proof whenever a goal is closed by reference; when that proof is disposed the
 * cached goals of the new proof are either completed by copying the referenced steps (settings
 * {@code DISPOSE_COPY}) or re-opened after removing the caching information (settings
 * {@code DISPOSE_REOPEN}).
 * <p>
 * The copy runs inside the mediator's auto-mode context (Swing parity,
 * CachingExtension.java:312-319: {@code mediator.initiateAutoMode(newProof, true, false)} around
 * the copy and {@code mediator.finishAutoMode(newProof, true, true, () -> {})} in the finally —
 * RESOLVED WP-4, KNOWN-SIMPLIFIED {@code CopyBeforeDisposeF.java:25}): the WP-1 seam publishes
 * the observable auto-mode state (the FX interface freeze) and flips the rule app index for the
 * duration of the copy. The resolver is only invoked directly when no mediator is available
 * (toolkit-free environments).
 *
 * @author Arne Keller (Swing original)
 * @author MP9.1 — WP9.1-2 copy-on-dispose listener port (FX)
 */
final class CopyBeforeDisposeF implements ProofDisposedListener {
    private static final Logger LOGGER = LoggerFactory.getLogger(CopyBeforeDisposeF.class);

    /** the mediator (for the auto-mode context around the copy), may be {@code null} */
    private final @Nullable KeYMediatorF mediator;

    /** the referenced proof that is about to be disposed */
    private final Proof referencedProof;

    /** the new proof whose cached branches reference {@link #referencedProof} */
    private final Proof newProof;

    /**
     * Construct a new listener.
     *
     * @param mediator the mediator, may be {@code null} (the copy then runs without the
     *        auto-mode context, like before WP-4)
     * @param referencedProof referenced proof
     * @param newProof new proof
     */
    CopyBeforeDisposeF(@Nullable KeYMediatorF mediator, Proof referencedProof, Proof newProof) {
        this.mediator = mediator;
        this.referencedProof = referencedProof;
        this.newProof = newProof;
    }

    @Override
    public void proofDisposing(ProofDisposedEvent event) {
        if (newProof.isDisposed()) {
            return;
        }
        if (CachingSettingsProviderF.getCachingSettings().getDispose()
                .equals(ProofCachingSettings.DISPOSE_COPY)) {
            try {
                KeYMediatorF m = mediator;
                if (m != null) {
                    m.initiateAutoMode(newProof, true, false);
                }
                CopyReferenceResolver.copyCachedGoals(newProof, referencedProof, null, null);
            } catch (RuntimeException ex) {
                // a failed copy must never take the proof disposal down with it
                LOGGER.error("failed to copy cached goals before disposing the referenced "
                    + "proof", ex);
            } finally {
                KeYMediatorF m = mediator;
                if (m != null) {
                    // Swing: finishAutoMode(newProof, true, true, () -> {}) — switch the rule
                    // app index back to interactive use and do not select a different node
                    m.finishAutoMode(newProof, true, true, () -> {
                    });
                }
            }
        } else {
            newProof.closedGoals().stream()
                    .filter(x -> x.node().lookup(ClosedBy.class) != null
                            && x.node().lookup(ClosedBy.class).proof() == referencedProof)
                    .forEach(x -> {
                        newProof.reOpenGoal(x);
                        x.node().deregister(x.node().lookup(ClosedBy.class), ClosedBy.class);
                    });
        }
    }

    @Override
    public void proofDisposed(ProofDisposedEvent event) {
    }
}

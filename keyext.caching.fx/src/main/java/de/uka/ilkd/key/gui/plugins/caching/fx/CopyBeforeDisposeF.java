/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.plugins.caching.fx;

import de.uka.ilkd.key.gui.plugins.caching.settings.ProofCachingSettings;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.event.ProofDisposedEvent;
import de.uka.ilkd.key.proof.event.ProofDisposedListener;
import de.uka.ilkd.key.proof.reference.ClosedBy;
import de.uka.ilkd.key.proof.reference.CopyReferenceResolver;

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
 * <b>KNOWN-SIMPLIFIED:</b> the Swing original wraps the copy into
 * {@code mediator.initiateAutoMode(...)}/{@code mediator.finishAutoMode(...)} (the UI
 * suspension/notifications of the Swing mediator, CachingExtension.java:312-319); the FX
 * {@link de.uka.ilkd.key.core.fx.KeYMediatorF} has no auto-mode context API for a foreign proof,
 * so the FX port invokes the same core operation (the {@link CopyReferenceResolver}) directly.
 *
 * @author Arne Keller (Swing original)
 * @author MP9.1 — WP9.1-2 copy-on-dispose listener port (FX)
 */
final class CopyBeforeDisposeF implements ProofDisposedListener {
    private static final Logger LOGGER = LoggerFactory.getLogger(CopyBeforeDisposeF.class);

    /** the referenced proof that is about to be disposed */
    private final Proof referencedProof;

    /** the new proof whose cached branches reference {@link #referencedProof} */
    private final Proof newProof;

    /**
     * Construct a new listener.
     *
     * @param referencedProof referenced proof
     * @param newProof new proof
     */
    CopyBeforeDisposeF(Proof referencedProof, Proof newProof) {
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
                CopyReferenceResolver.copyCachedGoals(newProof, referencedProof, null, null);
            } catch (RuntimeException ex) {
                // a failed copy must never take the proof disposal down with it
                LOGGER.error("failed to copy cached goals before disposing the referenced "
                    + "proof", ex);
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

/* This file is part of KeY - https://key-project.org
 * KeY is licensed by the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0 */
package de.uka.ilkd.key.proof.event;

import de.uka.ilkd.key.proof.Proof;

/**
 * Observes a {@link Proof}.
 *
 * @author Martin Hentschel
 */
public interface ProofDisposedListener {
    /**
     * When a {@link Proof} is going to be disposed.
     *
     * @param e The event.
     */
    public void proofDisposing(ProofDisposedEvent e);

    /**
     * When a {@link Proof} was disposed via {@link Proof#dispose()}.
     *
     * @param e The event.
     */
    public void proofDisposed(ProofDisposedEvent e);
}

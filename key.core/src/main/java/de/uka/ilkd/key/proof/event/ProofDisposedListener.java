/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
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
    void proofDisposing(ProofDisposedEvent e);

    /**
     * When a {@link Proof} was disposed via {@link Proof#dispose()}.
     *
     * @param e The event.
     */
    void proofDisposed(ProofDisposedEvent e);
}

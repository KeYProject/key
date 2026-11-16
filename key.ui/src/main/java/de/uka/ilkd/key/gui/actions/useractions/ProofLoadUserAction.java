/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.actions.useractions;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.proof.Proof;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * Virtual user action to undo loading a proof.
 *
 * @author Arne Keller
 */
@NullMarked
public class ProofLoadUserAction extends UserAction {
    /**
     * The proof loaded in this action.
     */
    private @Nullable Proof proofLoaded;

    /**
     * Construct a new user action of this kind.
     *
     * @param mediator mediator
     * @param proofLoaded the proof just loaded
     */
    public ProofLoadUserAction(KeYMediator mediator, Proof proofLoaded) {
        super(mediator, proofLoaded);
        this.proofLoaded = proofLoaded;
    }

    @Override
    public String name() {
        // {@code proofLoaded} becomes {@code null} after {@link #undo()}; in that (impossible for
        // a live action) state the previous code crashed with an NPE.
        return "Load: " + (proofLoaded == null ? "?" : proofLoaded.name());
    }

    @Override
    protected void apply() {
    }

    @Override
    public void undo() {
        if (proofLoaded != null) {
            proofLoaded.dispose();
            proofLoaded = null;
        }
    }

    @Override
    public boolean canUndo() {
        // {@code proofLoaded} is only {@code null} after an undo, which cannot be undone again.
        return proofLoaded != null && !proofLoaded.isDisposed();
    }
}

/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.actions.useractions;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.proof.Proof;

/**
 * User action to load a proof. Really just calls {@link KeYMediator#setProof(Proof)}.
 *
 * @author Arne Keller
 */
public class ProofLoadUserAction extends UserAction {
    /**
     * The proof loaded in this action.
     */
    private Proof proofLoaded;

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
        return "Load: " + proofLoaded.name();
    }

    @Override
    protected void apply() {
        mediator.setProof(proofLoaded);
    }

    @Override
    public void undo() {
        proofLoaded.dispose();
        proofLoaded = null;
    }

    @Override
    public boolean canUndo() {
        return !proofLoaded.isDisposed();
    }
}

/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.actions.useractions;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.proof.Proof;

/**
 * Abstract concept of an action performed by the user.
 * Has a name and may be applied or undone.
 * Always applied by {@link #actionPerformed(ActionEvent)}.
 *
 * @author Arne Keller
 */
public abstract class UserAction implements ActionListener {
    /**
     * KeY mediator. Used to register the execution of this user action.
     */
    protected final KeYMediator mediator;
    /**
     * The proof this action was applied on.
     */
    protected final Proof proof;

    /**
     * Set up this user action.
     *
     * @param mediator mediator
     * @param proof proof this action is to be applied on
     */
    protected UserAction(KeYMediator mediator, Proof proof) {
        this.mediator = mediator;
        this.proof = proof;
    }

    /**
     * @return the name of this action
     */
    public abstract String name();

    /**
     * Apply this user action. After a successive call to {@link #undo()}, it may not be possible
     * to re-apply the action!
     */
    protected abstract void apply();

    /**
     * Undo this user action. May only be done once.
     */
    public abstract void undo();

    /**
     * Whether this action can be undone given the current state of the proof.
     *
     * @return whether {@link #undo()} will work
     */
    public abstract boolean canUndo();

    @Override
    public void actionPerformed(ActionEvent e) {
        mediator.fireActionPerformed(this);
        apply();
    }

    public Proof getProof() {
        return proof;
    }
}

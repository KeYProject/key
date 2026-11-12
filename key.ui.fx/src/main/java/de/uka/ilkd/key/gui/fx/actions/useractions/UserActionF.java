/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.actions.useractions;

import de.uka.ilkd.key.core.fx.KeYMediatorF;
import de.uka.ilkd.key.proof.Proof;

import org.jspecify.annotations.NullMarked;

/**
 * Abstract concept of an action performed by the user, FX port of
 * {@code de.uka.ilkd.key.gui.actions.useractions.UserAction} (Swing UserAction.java:16-72):
 * has a name and may be applied or undone; always applied by {@link #actionPerformed()}, which
 * notifies the mediator's user-action listeners first ({@code fireActionPerformed}) and then
 * applies ({@link #apply()}).
 */
@NullMarked
public abstract class UserActionF {

    /** the FX mediator; used to register the execution of this user action. */
    protected final KeYMediatorF mediator;

    /** the proof this action was applied on. */
    protected final Proof proof;

    /**
     * Set up this user action.
     *
     * @param mediator the FX mediator
     * @param proof the proof this action is to be applied on
     */
    protected UserActionF(KeYMediatorF mediator, Proof proof) {
        this.mediator = mediator;
        this.proof = proof;
    }

    /** @return the name of this action */
    public abstract String name();

    /**
     * Apply this user action. After a successive call to {@link #undo()}, it may not be possible
     * to re-apply the action!
     */
    protected abstract void apply();

    /** Undo this user action. May only be done once. */
    public abstract void undo();

    /**
     * Whether this action can be undone given the current state of the proof.
     *
     * @return whether {@link #undo()} will work
     */
    public abstract boolean canUndo();

    /**
     * Notifies the user-action listeners and applies the action (Swing
     * {@code UserAction.actionPerformed}).
     */
    public void actionPerformed() {
        mediator.fireActionPerformed(this);
        apply();
    }

    /** @return the proof this action was applied on */
    public Proof getProof() {
        return proof;
    }
}

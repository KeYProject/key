package de.uka.ilkd.key.gui;

import de.uka.ilkd.key.core.KeYMediator;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

/**
 * Abstract concept of an action performed by the user.
 * Has a name and may be applied or undone.
 *
 * @author Arne Keller
 */
public abstract class UserAction implements ActionListener {
    /**
     * KeY mediator. Used to register the execution of this user action.
     */
    protected final KeYMediator mediator;

    /**
     * Set up this user action.
     *
     * @param mediator mediator
     */
    protected UserAction(KeYMediator mediator) {
        this.mediator = mediator;
    }

    /**
     * @return the name of this action
     */
    public abstract String name();

    /**
     * Apply this user action. After a successive call to {@link #undo()}, it may not be possible
     * to re-apply the action!
     */
    public abstract void apply();

    /**
     * Undo this user action. May only be done once.
     */
    public abstract void undo();

    @Override
    public void actionPerformed(ActionEvent e) {
        mediator.fireActionPerformed(this);
        apply();
    }
}

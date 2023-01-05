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
    protected final KeYMediator mediator;

    protected UserAction(KeYMediator mediator) {
        this.mediator = mediator;
    }

    public abstract String name();

    public abstract void apply();

    public abstract void undo();

    @Override
    public void actionPerformed(ActionEvent e) {
        mediator.fireActionPerformed(this);
        apply();
    }
}

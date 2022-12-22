package de.uka.ilkd.key.gui;

import de.uka.ilkd.key.core.KeYMediator;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

public abstract class UserAction implements ActionListener {
    protected final KeYMediator mediator;

    protected UserAction(KeYMediator mediator) {
        this.mediator = mediator;
    }

    public abstract void apply();

    public abstract void undo();

    @Override
    public void actionPerformed(ActionEvent e) {
        mediator.fireActionPerformed(this);
        apply();
    }
}

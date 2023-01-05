package de.uka.ilkd.key.gui;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.proof.Proof;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

/**
 * User action that represents the manual application of a rule.
 *
 * @author Arne Keller
 */
public class ProofRuleUserAction extends ProofModifyingUserAction {
    /**
     * Rule name.
     */
    private final String name;
    /**
     * Action listener that will be called on {@link #apply()}. Actual rule application will be
     * performed by this object.
     */
    private final ActionListener listener;
    /**
     * Action event to pass along to the listener.
     */
    private final ActionEvent event;

    /**
     * Construct a new user action of this kind.
     *
     * @param mediator mediator
     * @param proof proof
     * @param name name of the rule
     * @param listener action listener that will actually perform the rule application
     * @param event action event to pass to the listener
     */
    public ProofRuleUserAction(KeYMediator mediator, Proof proof, String name,
            ActionListener listener, ActionEvent event) {
        super(mediator, proof);
        this.name = name;
        this.listener = listener;
        this.event = event;
    }

    @Override
    public String name() {
        return "Apply: " + name;
    }

    @Override
    public void apply() {
        listener.actionPerformed(event);
    }
}

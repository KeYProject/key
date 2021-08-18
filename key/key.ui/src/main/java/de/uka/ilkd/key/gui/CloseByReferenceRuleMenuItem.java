package de.uka.ilkd.key.gui;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.CloseByReferenceRule;
import de.uka.ilkd.key.rule.CloseByReferenceRule.*;

import javax.swing.*;
import java.awt.event.ActionEvent;

/**
 * Menu item for the rule to close by reference.
 *
 * @author Wolfram Pfeifer
 * @see CloseByReferenceRule
 */
public class CloseByReferenceRuleMenuItem extends JMenuItem {
    public CloseByReferenceRuleMenuItem(Goal goal, Services services, KeYMediator mediator) {
        super();
        // note: the text of the menu item is set to the text of the action!
        this.setAction(new AbstractAction(toString()) {
            @Override
            public void actionPerformed(ActionEvent e) {
                CloseByReferenceRule rule = CloseByReferenceRule.INSTANCE;
                CloseByReferenceRuleApp app =
                    (CloseByReferenceRuleApp) rule.createApp(null, services);
                CloseByReferenceCompletion completion = CloseByReferenceCompletion.INSTANCE;
                CloseByReferenceRuleApp completedApp =
                    (CloseByReferenceRuleApp) completion.complete(app , goal, false);
                // The completedApp may be null if the completion was not possible.
                if (completedApp != null && completedApp.complete()) {
                    mediator.getUI().getProofControl().applyInteractive(completedApp, goal);
                }
            }
        });
    }

    @Override
    public String toString() {
        return "Close By Reference";
    }
}

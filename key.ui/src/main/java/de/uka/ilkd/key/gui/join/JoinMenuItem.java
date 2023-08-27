/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.join;

import java.awt.event.ActionEvent;
import java.util.List;
import javax.swing.*;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.notification.events.ExceptionFailureEvent;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.join.JoinProcessor;
import de.uka.ilkd.key.proof.join.JoinProcessor.Listener;
import de.uka.ilkd.key.proof.join.PredicateEstimator;
import de.uka.ilkd.key.proof.join.ProspectivePartner;

import org.key_project.util.collection.ImmutableList;

/**
 * The menu item for the "delayed-cut" join rule.
 *
 * @author Benjamin Niedermann
 * @see JoinProcessor
 */
public class JoinMenuItem extends JMenuItem {

    private static final long serialVersionUID = -2602116358650063634L;

    public JoinMenuItem(final List<ProspectivePartner> partner, final Proof proof,
            final KeYMediator mediator) {
        super();

        this.setText(toString());
        this.setAction(new AbstractAction(toString()) {

            private static final long serialVersionUID = 1L;

            @Override
            public void actionPerformed(ActionEvent e) {
                mediator.stopInterface(true);
                JoinDialog dialog = new JoinDialog(partner, proof, PredicateEstimator.STD_ESTIMATOR,
                    proof.getServices());
                dialog.setVisible(true);
                if (dialog.okButtonHasBeenPressed()) {
                    start(dialog.getSelectedPartner(), proof, mediator);
                } else {
                    mediator.startInterface(true);
                }

            }
        });
    }

    private void start(ProspectivePartner partner, Proof proof, final KeYMediator mediator) {


        JoinProcessor processor = new JoinProcessor(partner, proof);

        processor.addListener(new Listener() {

            @Override
            public void exceptionWhileJoining(Throwable e) {
                mediator.notify(new ExceptionFailureEvent(e.getMessage(), e));
                mediator.startInterface(true);
            }

            @Override
            public void endOfJoining(final ImmutableList<Goal> goals) {
                SwingUtilities.invokeLater(() -> {
                    mediator.startInterface(true);
                    // This method delegates the request only to the UserInterfaceControl which
                    // implements the functionality.
                    // No functionality is allowed in this method body!
                    mediator.getUI().getProofControl()
                            .startAutoMode(mediator.getSelectedProof(), goals);


                });


            }
        });

        Thread thread = new Thread(processor, "ProofJoinProcessor");
        thread.start();
    }


    @Override
    public String toString() {
        return "Delayed Cut Join Rule";
    }
}

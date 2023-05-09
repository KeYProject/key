package de.uka.ilkd.key.gui.plugins.caching;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import javax.swing.*;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.reference.ClosedBy;
import de.uka.ilkd.key.proof.reference.ReferenceSearcher;

public class ReferenceSearchButton extends JButton
        implements ActionListener, ReferenceSearchDialogListener {
    private final KeYMediator mediator;
    private ReferenceSearchDialog dialog = null;

    public ReferenceSearchButton(KeYMediator mediator) {
        super("Proof Caching");
        this.mediator = mediator;
        addActionListener(this);
    }


    @Override
    public void actionPerformed(ActionEvent e) {
        Proof p = mediator.getSelectedProof();
        for (Goal goal : p.openEnabledGoals()) {
            ClosedBy c = ReferenceSearcher.findPreviousProof(mediator.getCurrentlyOpenedProofs(),
                goal.node());
            if (c != null) {
                // p.closeGoal(goal);
                goal.setEnabled(false);

                goal.node().register(c, ClosedBy.class);
                c.getProof()
                        .addProofDisposedListener(new CloseReferenceExtension.CopyBeforeDispose(
                            mediator, c.getProof(), p));
            }
        }
        dialog = new ReferenceSearchDialog(p, this);
        dialog.setVisible(true);
    }

    @Override
    public void discardButtonClicked() {
        if (dialog != null) {
            dialog.dispose();
            dialog = null;
        }
    }

    @Override
    public void copyButtonClicked() {
        if (dialog != null) {
            mediator.getSelectedProof().copyCachedGoals(null);
            dialog.dispose();
            dialog = null;
        }
    }
}

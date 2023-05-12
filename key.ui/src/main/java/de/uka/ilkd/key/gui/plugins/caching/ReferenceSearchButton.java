package de.uka.ilkd.key.gui.plugins.caching;

import java.awt.*;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import javax.swing.*;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.gui.colors.ColorSettings;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.reference.ClosedBy;
import de.uka.ilkd.key.proof.reference.ReferenceSearcher;

public class ReferenceSearchButton extends JButton
        implements ActionListener, ReferenceSearchDialogListener, KeYSelectionListener {
    /**
     * Color used for the label if a reference is found.
     */
    private static final ColorSettings.ColorProperty COLOR_FINE =
        ColorSettings.define("caching.reference_found", "",
            new Color(80, 120, 0));

    private final KeYMediator mediator;
    private ReferenceSearchDialog dialog = null;

    public ReferenceSearchButton(KeYMediator mediator) {
        super("Proof Caching");
        this.mediator = mediator;
        mediator.addKeYSelectionListener(this);
        addActionListener(this);
        setEnabled(false);
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
            mediator.stopInterface(true);
            new Thread(() -> mediator.getSelectedProof().copyCachedGoals(null,
                total -> SwingUtilities.invokeLater(() -> dialog.setMaximum(total)),
                () -> SwingUtilities.invokeLater(() -> {
                    if (dialog.incrementProgress()) {
                        mediator.startInterface(true);
                        dialog.dispose();
                        dialog = null;
                    }
                }))).start();
        }
    }

    @Override
    public void selectedNodeChanged(KeYSelectionEvent e) {
        Proof p = e.getSource().getSelectedProof();
        if (p == null) {
            setText("Proof Caching");
            setForeground(null);
            setEnabled(false);
            return;
        }
        long foundRefs =
            p.openGoals().stream().filter(g -> g.node().lookup(ClosedBy.class) != null).count();
        if (foundRefs > 0) {
            setText(String.format("Proof Caching (%d)", foundRefs));
            setForeground(COLOR_FINE.get());
            setEnabled(true);
        } else {
            setText("Proof Caching");
            setForeground(null);
            setEnabled(false);
        }
    }
}

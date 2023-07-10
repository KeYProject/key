package de.uka.ilkd.key.gui.plugins.caching;

import javax.swing.*;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.ShowProofStatistics;
import de.uka.ilkd.key.proof.Proof;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

public class DefaultReferenceSearchDialogListener implements ReferenceSearchDialogListener {
    private static final Logger LOGGER =
        LoggerFactory.getLogger(DefaultReferenceSearchDialogListener.class);
    private final KeYMediator mediator;

    public DefaultReferenceSearchDialogListener(KeYMediator mediator) {
        this.mediator = mediator;
    }

    @Override
    public void closeButtonClicked(ReferenceSearchDialog dialog) {
        dialog.dispose();
    }

    @Override
    public void copyButtonClicked(ReferenceSearchDialog dialog) {
        System.out.println("copy clicked !!!");
        mediator.stopInterface(true);
        Proof p = mediator.getSelectedProof();
        new Thread(() -> {
            try {
                p.copyCachedGoals(null,
                    total -> SwingUtilities.invokeLater(() -> dialog.setMaximum(total)),
                    () -> SwingUtilities.invokeLater(() -> {
                        if (dialog.incrementProgress()) {
                            mediator.startInterface(true);
                            dialog.dispose();
                            new ShowProofStatistics.Window(MainWindow.getInstance(), p)
                                    .setVisible(true);
                        }
                    }));
            } catch (Exception e) {
                LOGGER.error("failed to copy cache ", e);
            }
        }).start();
    }
}

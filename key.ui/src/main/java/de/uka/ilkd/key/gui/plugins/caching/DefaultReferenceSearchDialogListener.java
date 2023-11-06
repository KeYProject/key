/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.plugins.caching;

import java.util.function.Consumer;
import javax.swing.*;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.IssueDialog;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.ShowProofStatistics;
import de.uka.ilkd.key.proof.Proof;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * The default controller for the {@link ReferenceSearchDialog}.
 * When the copy button is clicked, {@link Proof#copyCachedGoals(Proof, Consumer, Runnable)}
 * is started.
 *
 * @author Arne Keller
 */
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
                mediator.startInterface(true);
                LOGGER.error("failed to copy cache ", e);
                IssueDialog.showExceptionDialog(dialog, new CachingException(e));
            }
        }).start();
    }
}

/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.plugins.caching.fx;

import javafx.stage.Window;

import de.uka.ilkd.key.core.fx.KeYMediatorF;
import de.uka.ilkd.key.gui.fx.IssueDialogF;
import de.uka.ilkd.key.gui.fx.notification.ProofStatisticsDialogF;
import de.uka.ilkd.key.gui.plugins.caching.CachingException;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.reference.CopyReferenceResolver;

import org.key_project.util.javafx.FxUtil;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * The default controller for the {@link ReferenceSearchDialogF}, FX port of
 * {@code DefaultReferenceSearchDialogListener} (Swing
 * DefaultReferenceSearchDialogListener.java:28-69). When the copy button is clicked,
 * {@link CopyReferenceResolver#copyCachedGoals(Proof, Proof, java.util.function.Consumer,
 * Runnable)} is started on a background thread, wrapped into the mediator's auto-mode context
 * (Swing {@code mediator.stopInterface(true)} + {@code initiateAutoMode}/{@code
 * finishAutoMode}; in the FX UI the freeze is the observable {@code autoModeRunning} property
 * published by the WP-1 seam, so the extra interface-stop call is not needed), and the proof
 * statistics window is opened once every branch has been copied (Swing
 * {@code ShowProofStatistics.Window}).
 *
 * @author Arne Keller (Swing original)
 * @author WP-4 dialog port (FX)
 */
final class DefaultReferenceSearchDialogListenerF implements ReferenceSearchDialogListenerF {
    private static final Logger LOGGER =
        LoggerFactory.getLogger(DefaultReferenceSearchDialogListenerF.class);

    private final KeYMediatorF mediator;

    /** the owner window for the issue dialog and the statistics window */
    private final Window owner;

    DefaultReferenceSearchDialogListenerF(KeYMediatorF mediator, Window owner) {
        this.mediator = mediator;
        this.owner = owner;
    }

    @Override
    public void closeButtonClicked(ReferenceSearchDialogF dialog) {
        dialog.close();
    }

    @Override
    public void copyButtonClicked(ReferenceSearchDialogF dialog) {
        Proof p = mediator.getSelectedProof();
        new Thread(() -> {
            try {
                mediator.initiateAutoMode(p, true, false);
                CopyReferenceResolver.copyCachedGoals(p, null,
                    total -> FxUtil.runLater(() -> dialog.setMaximum(total)),
                    () -> FxUtil.runLater(() -> {
                        if (dialog.incrementProgress()) {
                            dialog.close();
                            ProofStatisticsDialogF.show(owner, p);
                        }
                    }));
            } catch (Exception e) {
                LOGGER.error("failed to copy cache ", e);
                IssueDialogF.showExceptionDialog(owner, new CachingException(e));
            } finally {
                mediator.finishAutoMode(p, true, false, () -> {
                    mediator.getSelectionModel().setSelectedNode(p.root());
                });
            }
        }, "ReferenceSearchDialog copy").start();
    }
}

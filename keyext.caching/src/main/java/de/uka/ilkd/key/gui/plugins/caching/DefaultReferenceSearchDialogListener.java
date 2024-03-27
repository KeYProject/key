/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.plugins.caching;

import java.lang.reflect.InvocationTargetException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;
import javax.swing.*;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.IssueDialog;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.ShowProofStatistics;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.reference.ClosedBy;

import org.key_project.util.GenericWorker;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * The default controller for the {@link ReferenceSearchDialog}.
 * When the copy button is clicked, all cached branches are realized.
 *
 * @author Arne Keller
 */
public class DefaultReferenceSearchDialogListener implements ReferenceSearchDialogListener {
    private static final Logger LOGGER =
        LoggerFactory.getLogger(DefaultReferenceSearchDialogListener.class);

    /**
     * The caching extension.
     */
    private final CachingExtension extension;
    /**
     * The KeY mediator.
     */
    private final KeYMediator mediator;

    /**
     * Create a new listener object.
     *
     * @param mediator the KeY mediator
     */
    public DefaultReferenceSearchDialogListener(CachingExtension extension, KeYMediator mediator) {
        this.extension = extension;
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
        var worker = new GenericWorker<>(() -> {
            copyAllReferencedBranches(p, dialog);
            return 0;
        }, _x -> mediator.startInterface(true), exc -> {
            LOGGER.error("unexpected failure when copying from proof cache ", exc);
            IssueDialog.showExceptionDialog(dialog, new CachingException(exc));
        });
        worker.execute();
    }

    /**
     * Copy (realize) all referenced branches in the specified proof.
     *
     * @param proof the proof to realize
     * @param dialog open reference search dialog
     * @throws InterruptedException on Swing error
     * @throws InvocationTargetException on Swing error
     */
    private void copyAllReferencedBranches(Proof proof, ReferenceSearchDialog dialog)
            throws InterruptedException, InvocationTargetException {
        // first, load externally referenced goals
        var externalsToGet = proof.closedGoals().stream()
                .filter(x -> x.node().lookup(CachedProofBranch.class) != null)
                .collect(
                    Collectors.groupingBy(x -> x.node().lookup(CachedProofBranch.class).proofFile));
        List<Proof> auxiliaryProofs = new ArrayList<>();
        SwingUtilities.invokeAndWait(() -> {
            dialog.setProgressBarString("Loading cached proofs from external database...");
            dialog.setMaximum(externalsToGet.size());
        });
        for (var externalToGet : externalsToGet.entrySet()) {
            Map<Integer, List<Goal>> goalsByStepIndex = new HashMap<>();
            // deregister the references
            var goals = externalToGet.getValue();
            for (var goal : goals) {
                var cachedBranch = goal.node().lookup(CachedProofBranch.class);
                goalsByStepIndex.computeIfAbsent(cachedBranch.stepIndex, _x -> new ArrayList<>())
                        .add(goal);
                goal.node().deregister(cachedBranch, CachedProofBranch.class);
            }
            var filename = externalToGet.getKey();
            Proof externalProof = null;
            // try to load the proof again
            try {
                externalProof = KeYEnvironment.load(filename).getLoadedProof();
            } catch (Exception exception) {
                LOGGER.error("failed to load referenced proof ", exception);
                IssueDialog.showExceptionDialog(MainWindow.getInstance(), exception);
                continue;
            }
            auxiliaryProofs.add(externalProof);
            // create new ClosedBy associations
            externalProof.setStepIndices();
            var allNodes = externalProof.root().subtreeIterator();
            while (allNodes.hasNext()) {
                var x = allNodes.next();
                var goalsReferencingX = goalsByStepIndex.get(x.getStepIndex());
                if (goalsReferencingX != null) {
                    for (var goal : goalsReferencingX) {
                        goal.node().register(new ClosedBy(externalProof, x, Set.of()),
                            ClosedBy.class);
                    }
                }
            }
            SwingUtilities.invokeAndWait(dialog::incrementProgress);
        }
        // then, take care of all the regular ClosedBy links
        SwingUtilities.invokeAndWait(() -> dialog.setProgressBarString("Copying cached goals..."));
        try {
            proof.copyCachedGoals(null,
                total -> {
                    try {
                        SwingUtilities.invokeAndWait(() -> dialog.setMaximum(total));
                    } catch (InterruptedException | InvocationTargetException e) {
                        throw new RuntimeException(e);
                    }
                },
                () -> SwingUtilities.invokeLater(() -> {
                    if (dialog.incrementProgress()) {
                        dialog.dispose();
                        // close auxiliary proofs
                        auxiliaryProofs.forEach(Proof::dispose);
                        mediator.startInterface(true);
                        extension.updateGUIState();
                        new ShowProofStatistics.Window(MainWindow.getInstance(), proof)
                                .setVisible(true);
                    }
                }));
        } catch (Exception e) {
            LOGGER.error("failed to copy cached proof ", e);
            IssueDialog.showExceptionDialog(MainWindow.getInstance(), new CachingException(e));
        }
    }
}

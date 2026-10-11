/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2,
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.plugins.caching.fx;

import java.util.Set;
import javafx.stage.Window;

import de.uka.ilkd.key.core.fx.KeYMediatorF;
import de.uka.ilkd.key.gui.fx.extension.KeYGuiExtensionFacadeF;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.reference.ClosedBy;
import de.uka.ilkd.key.settings.GeneralSettings;

import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Headless verify harness for the caching extension parity work ({@code key.fx.verify.caching},
 * forwarded by key.ui.fx/build.gradle and invoked reflectively by {@code MainWindowF}): a
 * self test of the ported interactive reference-search dialog —
 * <ol>
 * <li>the opened-proofs seam: {@link CachingExtensionF#openedProofs()} feeds
 * {@code mediator.getCurrentlyOpenedProofs()} (the live WP-1 list, KNOWN-SIMPLIFIED
 * {@code CachingExtensionF.java:778}),</li>
 * <li>the dialog renders the per-goal reference table of the loaded proof, the "Apply" button
 * is disabled without references and enabled when a (stub) {@link ClosedBy} reference is
 * present, and the row reports the referenced proof's index among the opened proofs,</li>
 * <li>the Apply wiring fires the dialog listener and disables the Apply/Close buttons, and the
 * progress reporting runs through {@code setMaximum}/{@code incrementProgress} —</li>
 * </ol>
 * <b>without running a real caching copy</b>: the listener is a recording stub (fake/stub data
 * like the Swing dialog tests) and the stub reference is deregistered after the run.
 * <p>
 * The harness must be called on the JavaFX thread after a demo proof has been loaded.
 */
public final class CachingVerifyF {

    private static final Logger LOGGER = LoggerFactory.getLogger(CachingVerifyF.class);

    private CachingVerifyF() {
    }

    /**
     * Runs the reference-search self test.
     *
     * @param owner the owner window for the dialog
     * @param proof the loaded demo proof (its goals fill the table)
     * @param mediator the application mediator
     * @return the one-line report ending in {@code PASS} or {@code FAIL}
     */
    public static String run(Window owner, @Nullable Proof proof, KeYMediatorF mediator) {
        if (proof == null) {
            return "Caching reference-search verify: SKIP (no proof loaded)";
        }
        ReferenceSearchDialogF dialog = null;
        Node stubNode = null;
        ClosedBy stubReference = null;
        Goal stubGoal = null;
        // the closed-goal list is only maintained when pruning closed branches is allowed
        // (GeneralSettings.noPruningClosed, default true — the core caching copy test
        // TestCopyingReplayer also runs with the setting off); save and restore it
        boolean oldNoPruningClosed = GeneralSettings.noPruningClosed;
        GeneralSettings.noPruningClosed = false;
        try {
            // (1) opened-proofs seam (KNOWN-SIMPLIFIED CachingExtensionF.java:778): the
            // extension scans the mediator's live opened-proofs list
            CachingExtensionF extension = findExtension();
            check(extension != null, "caching extension registered via the service loader");
            if (extension != null) {
                check(extension.openedProofs() == mediator.getCurrentlyOpenedProofs(),
                    "openedProofs() is the mediator's opened-proofs list (WP-1 seam)");
                check(extension.openedProofs().contains(proof),
                    "the loaded demo proof is among the opened proofs");
            }

            // (2) dialog render with the demo proof's goals — no reference rows yet
            RecordingListener listener = new RecordingListener();
            dialog = new ReferenceSearchDialogF(owner, proof, mediator, listener);
            dialog.show();
            check(dialog.isShowing(), "dialog renders");
            check(dialog.rowCount() > 0, "table lists the goals of the loaded proof");
            check(!dialog.cellText(0, 0).isEmpty(), "goal column shows the node serial number");
            for (int row = 0; row < dialog.rowCount(); row++) {
                check("no reference found".equals(dialog.cellText(row, 1)),
                    "row " + row + " reports no reference before the stub is registered");
            }
            check(!dialog.isApplyEnabled(), "Apply disabled without a ClosedBy reference");

            // stub ClosedBy on the first open goal's node (self-reference — fake/stub data,
            // like the Swing dialog tests; no real caching run). The goal is closed and
            // referenced exactly like the real close-by-reference flow does
            // (CachingExtensionF.closeByReference: closeGoal + register ClosedBy), because the
            // "Apply" button is only enabled for goals closed by reference (Swing
            // ReferenceSearchDialog.java:98-100). The state is restored in the finally block.
            Goal goal = proof.openGoals().stream().findFirst().orElse(null);
            check(goal != null, "the demo proof has an open goal");
            if (goal != null) {
                stubNode = goal.node();
                stubGoal = goal;
                stubReference = new ClosedBy(proof, stubNode, Set.of());
                proof.closeGoal(goal);
                stubNode.register(stubReference, ClosedBy.class);
                // the table is a construction-time snapshot (Swing parity): rebuild the dialog
                dialog.close();
                dialog = new ReferenceSearchDialogF(owner, proof, mediator, listener);
                dialog.show();
                int referenceRow = findReferenceRow(dialog);
                check(referenceRow >= 0, "a row reports the stub reference");
                if (referenceRow >= 0) {
                    check(
                        dialog.cellText(referenceRow, 1)
                                .equals(String.format("reference available (proof %d, node %d)",
                                    mediator.getCurrentlyOpenedProofs().indexOf(proof) + 1,
                                    stubNode.serialNr())),
                        "reference row shows the opened-proofs index and the node serial ('"
                            + dialog.cellText(referenceRow, 1) + "')");
                }
                check(dialog.isApplyEnabled(), "Apply enabled with a ClosedBy reference");

                // (3) Apply wiring: the click fires the listener and disables the buttons
                // (Swing ReferenceSearchDialog.getApplyButton, ReferenceSearchDialog.java
                // :112-122)
                dialog.apply();
                check(listener.copyClicked, "Apply fired the dialog listener");
                check(!dialog.isApplyEnabled(), "Apply disabled after the click");
                check(!dialog.isCloseEnabled(), "Close disabled after the click");
            }

            // progress reporting (Swing setMaximum/incrementProgress)
            dialog.setMaximum(2);
            check("Working...".equals(dialog.progressText()), "progress reports 'Working...'");
            check(!dialog.incrementProgress(), "progress not full after the first branch");
            check(dialog.incrementProgress(), "progress full after the last branch");
            check("Finished.".equals(dialog.progressText()), "progress reports 'Finished.'");

            // close wiring
            dialog.close();
            check(!dialog.isShowing(), "dialog closed");

            LOGGER.info("Caching reference-search verify: dialog renders, stub reference row, "
                + "Apply wiring and progress reporting OK (no real caching copy run)");
            return "Caching reference-search verify: dialog renders + Apply wiring without a "
                + "real caching run PASS";
        } catch (RuntimeException | AssertionError e) {
            LOGGER.error("Caching reference-search verify failed", e);
            return "Caching reference-search verify: FAIL (" + e + ")";
        } finally {
            GeneralSettings.noPruningClosed = oldNoPruningClosed;
            if (stubNode != null && stubReference != null) {
                stubNode.deregister(stubReference, ClosedBy.class);
            }
            if (stubGoal != null) {
                // restore the demo proof state: re-open the goal closed for the stub reference
                Goal closedGoal = proof.getClosedGoal(stubGoal.node());
                if (closedGoal != null) {
                    proof.reOpenGoal(closedGoal);
                }
            }
            if (dialog != null) {
                dialog.close();
            }
        }
    }

    private static int findReferenceRow(ReferenceSearchDialogF dialog) {
        for (int row = 0; row < dialog.rowCount(); row++) {
            if (dialog.cellText(row, 1).startsWith("reference available")) {
                return row;
            }
        }
        return -1;
    }

    private static CachingExtensionF findExtension() {
        return KeYGuiExtensionFacadeF.getExtensions().stream()
                .filter(CachingExtensionF.class::isInstance)
                .map(CachingExtensionF.class::cast).findFirst().orElse(null);
    }

    private static void check(boolean condition, String what) {
        if (!condition) {
            throw new AssertionError("Caching reference-search verify: " + what + " — failed");
        }
    }

    /**
     * Recording stub listener: only counts the Apply clicks (the real copy is the
     * {@link DefaultReferenceSearchDialogListenerF}, exercised with a stub here so no real
     * caching copy is run).
     */
    private static final class RecordingListener implements ReferenceSearchDialogListenerF {
        boolean copyClicked;

        @Override
        public void copyButtonClicked(ReferenceSearchDialogF dialog) {
            copyClicked = true;
        }

        @Override
        public void closeButtonClicked(ReferenceSearchDialogF dialog) {
            dialog.close();
        }
    }
}

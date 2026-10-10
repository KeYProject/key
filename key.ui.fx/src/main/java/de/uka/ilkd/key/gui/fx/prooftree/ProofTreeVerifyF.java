/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.prooftree;

import java.util.concurrent.CountDownLatch;
import java.util.concurrent.TimeUnit;
import javafx.application.Platform;
import javafx.stage.Window;

import de.uka.ilkd.key.gui.fx.notification.NotificationManagerF;
import de.uka.ilkd.key.gui.fx.notification.NotificationManagerF.Kind;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * prooftree (P3a): self-test harness for the {@code key.fx.verify.prooftree} hook. Exercises the
 * C19-C23/C25/C27 parity items:
 * <ul>
 * <li>the tree semantics self test ({@link ProofTreeViewF#verifyProoftreeSemantics}): the
 * per-proof view-state cache (C19), the linearized mode (C20), the OSS protocol rows and the
 * "expand OSS nodes" toggle (C21), the whole-tree expand/collapse (C22) and the node-filter
 * counting rule (C25);</li>
 * <li>the two P3a popup dialogs (C23): the proof node notes editor stores its input via the OK
 * seam, the subtree statistics dialog opens and closes;</li>
 * <li>a report of the auto-mode partial-update counters (C27).</li>
 * </ul>
 */
public final class ProofTreeVerifyF {

    private static final Logger LOGGER = LoggerFactory.getLogger(ProofTreeVerifyF.class);

    private ProofTreeVerifyF() {
    }

    /**
     * Runs the self test. Must be called on the FX thread (from the {@code key.fx.verify.prooftree}
     * dispatch in the main window); the dialog waits run on a worker thread like the P2b harness.
     *
     * @param owner the owner window (unused; kept for API symmetry with the other harnesses)
     * @param proof the loaded demo proof, may be {@code null}
     * @param view the proof tree view under test
     * @return a short status message; the full report arrives via the status line and a
     *         notification
     */
    public static String run(Window owner, Proof proof, ProofTreeViewF view) {
        if (proof == null) {
            LOGGER.warn("Proof tree verification: no proof loaded — SKIP");
            return "SKIP (no proof)";
        }
        Thread worker = new Thread(() -> {
            String report = runAll(proof, view);
            LOGGER.info("Proof tree verification: {}", report);
            Platform.runLater(() -> NotificationManagerF.getInstance()
                    .notify("Proof tree verification: " + report,
                        report.startsWith("PASS") ? Kind.INFO : Kind.ERROR));
        }, "fx-verify-prooftree");
        worker.setDaemon(true);
        worker.start();
        return "running (see log)";
    }

    private static String runAll(Proof proof, ProofTreeViewF view) {
        StringBuilder problems = new StringBuilder();
        StringBuilder notes = new StringBuilder();

        // C27: snapshot the auto-mode counters *before* the semantics self test — the C19
        // view-state section switches proofs via setProof, which resets the live counters
        String autoModeReport = view.getAutoModeReport();

        // C19-C22/C25: the tree semantics self test (touches the TreeView — FX thread only)
        CountDownLatch treeLatch = new CountDownLatch(1);
        runOnFx(() -> {
            try {
                notes.append(view.verifyProoftreeSemantics());
            } finally {
                treeLatch.countDown();
            }
        });
        awaitLatch(treeLatch, "prooftree semantics self test", problems);

        // C23: the notes editor stores the input on the node via the OK seam (Swing
        // ProofTreePopupFactory.Notes), empty input clears the note
        Node target = proof.root();
        ProofTreeNotesDialogF[] dialogRef = new ProofTreeNotesDialogF[1];
        runOnFx(() -> dialogRef[0] = new ProofTreeNotesDialogF(null, target));
        ProofTreeNotesDialogF notesDialog = dialogRef[0];
        runOnFx(notesDialog::showNonBlocking);
        waitUntil(() -> notesDialog.getStage().isShowing(), "notes dialog shows", problems);
        String noteBefore = target.getNodeInfo().getNotes();
        if (noteBefore != null && !noteBefore.isEmpty()) {
            problems.append("notes dialog: pre-existing note not expected; ");
        }
        runOnFx(() -> {
            notesDialog.textArea.setText("P3a verify note");
            notesDialog.requestOk();
        });
        waitUntil(() -> !notesDialog.getStage().isShowing(), "notes dialog closes on ok", problems);
        if (!"P3a verify note".equals(target.getNodeInfo().getNotes())) {
            problems.append("notes dialog: stored note mismatch; ");
        } else {
            notes.append(" notes=PASS");
        }
        // clear the test note again so the demo proof stays clean
        runOnFx(() -> target.getNodeInfo().setNotes(null));

        // C23: the subtree statistics dialog opens and closes; the report contains the goal and
        // rule-application counters (ShowProofStatistics port)
        SubtreeStatisticsDialogF[] statsRef = new SubtreeStatisticsDialogF[1];
        runOnFx(() -> statsRef[0] = new SubtreeStatisticsDialogF(proof.root()));
        SubtreeStatisticsDialogF statsDialog = statsRef[0];
        runOnFx(statsDialog::showNonBlocking);
        waitUntil(() -> statsDialog.getStage().isShowing(), "subtree statistics dialog shows",
            problems);
        String statsText = SubtreeStatisticsDialogF.renderReport(proof.root());
        if (!statsText.contains("Open goals")) {
            problems.append("subtree statistics: report missing goal counters; ");
        }
        runOnFx(statsDialog::requestOk);
        waitUntil(() -> !statsDialog.getStage().isShowing(),
            "subtree statistics dialog closes", problems);

        notes.append(' ').append(autoModeReport);

        boolean pass = problems.length() == 0 && notes.toString().contains("PASS");
        return (pass ? "PASS" : "FAIL") + ": " + notes + " "
            + (problems.length() > 0 ? "problems=[" + problems + "]" : "problems=[]");
    }

    /** Polls a condition with a timeout (the FX runLater queue keeps the modal loop alive). */
    private static boolean waitUntil(java.util.function.BooleanSupplier condition, String what,
            StringBuilder problems) {
        long deadline = System.currentTimeMillis() + 10_000;
        while (System.currentTimeMillis() < deadline && !condition.getAsBoolean()) {
            try {
                Thread.sleep(25);
            } catch (InterruptedException e) {
                Thread.currentThread().interrupt();
                problems.append("interrupted waiting for ").append(what).append("; ");
                return false;
            }
        }
        if (!condition.getAsBoolean()) {
            problems.append("timed out waiting for ").append(what).append("; ");
            return false;
        }
        return true;
    }

    /** Runs {@code runnable} on the FX thread and blocks until it completed. */
    private static void runOnFx(Runnable runnable) {
        if (Platform.isFxApplicationThread()) {
            runnable.run();
            return;
        }
        CountDownLatch latch = new CountDownLatch(1);
        Platform.runLater(() -> {
            try {
                runnable.run();
            } finally {
                latch.countDown();
            }
        });
        awaitLatch(latch, "fx task", new StringBuilder());
    }

    /** Blocks until the latch is released or the timeout expires. */
    private static void awaitLatch(CountDownLatch latch, String what, StringBuilder problems) {
        try {
            if (!latch.await(10, TimeUnit.SECONDS)) {
                problems.append("timed out waiting for ").append(what).append("; ");
            }
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
            problems.append("interrupted waiting for ").append(what).append("; ");
        }
    }
}

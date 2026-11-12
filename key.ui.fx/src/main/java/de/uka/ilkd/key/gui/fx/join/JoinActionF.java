/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.join;

import java.util.List;
import javafx.application.Platform;
import javafx.stage.Window;

import de.uka.ilkd.key.control.ProofControl;
import de.uka.ilkd.key.gui.fx.notification.NotificationManagerF;
import de.uka.ilkd.key.gui.fx.notification.NotificationManagerF.Kind;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.join.JoinProcessor;
import de.uka.ilkd.key.proof.join.JoinProcessor.Listener;
import de.uka.ilkd.key.proof.join.PredicateEstimator;
import de.uka.ilkd.key.proof.join.ProspectivePartner;

import org.key_project.util.collection.ImmutableList;

// joinmerge: TODO-merge register with WindowUserInterfaceControlF completion registry —
// this action is the trigger counterpart of Swing's JoinMenuItem; once the FX rule-application
// context menu exists (CurrentGoalViewMenu port), wire it there and hand in the proof control
// from the mediator.

/**
 * The trigger of the interactive "delayed cut" join rule: shows the {@link JoinDialogF} and, if
 * the user confirms, starts the core {@link JoinProcessor} on a background thread and — like the
 * Swing original — restarts the automatic mode on the joined goals when the processing finished.
 * Counter-part of {@code de.uka.ilkd.key.gui.join.JoinMenuItem} in the Swing module
 * {@code key.ui} (JoinMenuItem.java:28-90).
 * <p>
 * Event semantics ported from Swing:
 * <ul>
 * <li>the dialog is modal; only a confirmed OK starts the join (JoinMenuItem.java:42-51);</li>
 * <li>the {@code JoinProcessor.Listener} results are marshalled back onto the UI thread with
 * {@code Platform.runLater} instead of {@code SwingUtilities.invokeLater}
 * (JoinMenuItem.java:60-79);</li>
 * <li>exceptions during joining are reported to the notification layer (Swing forwards an
 * {@code ExceptionFailureEvent} to the mediator, JoinMenuItem.java:62-65; the FX port raises an
 * ERROR toast on {@link NotificationManagerF});</li>
 * <li>the end of joining starts the auto mode on the joined goals via the proof control
 * (JoinMenuItem.java:68-78).</li>
 * </ul>
 * Deviations: the Swing menu item class is not ported as a menu item — the FX UI has no rule
 * application context menu yet, so the trigger is a plain entry point taking the proof control
 * (this is the seam {@code mediator.getUI().getProofControl()} of Swing JoinMenuItem.java:73-74);
 * the Swing {@code mediator.stopInterface(true)} UI lock (JoinMenuItem.java:48) has no FX
 * counterpart yet and is not ported.
 */
public final class JoinActionF {

    /** Menu text of the Swing original (JoinMenuItem.toString, JoinMenuItem.java:87-89). */
    public static final String TEXT = "Delayed Cut Join Rule";

    private JoinActionF() {
    }

    /**
     * Opens the join dialog for the given partner candidates and starts the join on
     * confirmation.
     *
     * @param partners the prospective join partners (computed by the caller via
     *        {@code JoinIsApplicable.INSTANCE.isApplicable(...)}, cf. Swing
     *        CurrentGoalViewMenu.java:235-238)
     * @param proof the proof to join
     * @param proofControl the proof control used to restart the auto mode (Swing
     *        {@code mediator.getUI().getProofControl()})
     * @param owner the owner window for the dialog (may be {@code null})
     */
    public static void run(List<ProspectivePartner> partners, Proof proof,
            ProofControl proofControl, Window owner) {
        JoinDialogF dialog =
            new JoinDialogF(partners, proof, PredicateEstimator.STD_ESTIMATOR,
                proof.getServices(), owner);
        dialog.show(owner);
        if (dialog.okButtonHasBeenPressed()) {
            start(dialog.getSelectedPartner(), proof, proofControl);
        }
    }

    /**
     * Swing JoinMenuItem.start (JoinMenuItem.java:55-83): run the processor on a background
     * thread and deliver its results on the UI thread.
     */
    private static void start(ProspectivePartner partner, Proof proof, ProofControl proofControl) {
        JoinProcessor processor = new JoinProcessor(partner, proof);

        processor.addListener(new Listener() {

            @Override
            public void exceptionWhileJoining(Throwable e) {
                Platform.runLater(() -> NotificationManagerF.getInstance()
                        .notify("Joining failed: " + e.getMessage(), Kind.ERROR));
            }

            @Override
            public void endOfJoining(ImmutableList<Goal> goals) {
                // This method delegates the request only to the UserInterfaceControl which
                // implements the functionality. No functionality is allowed in this method body!
                // (comment of Swing JoinMenuItem.java:70-74)
                Platform.runLater(() -> proofControl.startAutoMode(proof, goals));
            }
        });

        Thread thread = new Thread(processor, "ProofJoinProcessor");
        thread.start();
    }
}

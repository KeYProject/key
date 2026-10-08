/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.join;

import java.util.ArrayList;
import java.util.List;
import javafx.application.Platform;
import javafx.stage.Stage;
import javafx.stage.Window;

import de.uka.ilkd.key.control.ProofControl;
import de.uka.ilkd.key.gui.fx.mergerule.MergePartnerSelectionDialogF;
import de.uka.ilkd.key.gui.fx.mergerule.MergeRuleCompletionF;
import de.uka.ilkd.key.gui.fx.mergerule.MergeRuleMenuItemF;
import de.uka.ilkd.key.gui.fx.mergerule.predicateabstraction.AbstractionPredicatesChoiceDialogF;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.join.JoinIsApplicable;
import de.uka.ilkd.key.proof.join.PredicateEstimator;
import de.uka.ilkd.key.proof.join.ProspectivePartner;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.rule.merge.MergePartner;
import de.uka.ilkd.key.rule.merge.MergeRule;
import de.uka.ilkd.key.rule.merge.MergeRuleBuiltInRuleApp;

import org.key_project.logic.PosInTerm;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.util.collection.ImmutableList;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Interactive self test for the join/merge dialog ports ({@code key.fx.verify.joinmerge=1},
 * forwarded by {@code key.ui.fx/build.gradle}). The dialogs are normally triggered by the rule
 * completion dispatch / the sequent context menu, which do not exist in the JavaFX UI yet — this
 * harness therefore constructs them directly:
 * <ol>
 * <li>run a <em>limited</em> automatic strategy run on the loaded demo proof to create open
 * branches stuck at the join/merge points;</li>
 * <li>compute the join partners with the same core call the Swing context menu uses
 * ({@code JoinIsApplicable.INSTANCE.isApplicable}, Swing {@code CurrentGoalViewMenu.java:235});
 * </li>
 * <li>open the {@link JoinDialogF} non-blocking on the FX thread, drive the partner selection,
 * the predicate input and the OK/Cancel actions programmatically, and compare the OK enablement
 * with the Swing enablement logic (valid input AND applicable partner, Swing
 * {@code JoinDialog.java:43,132-141});</li>
 * <li>find a merge rule application of admissible form ({@link MergeRule#isApplicable}) with
 * potential merge partners and check the <em>forced</em> (headless) completion of
 * {@link MergeRuleCompletionF#INSTANCE};</li>
 * <li>open the {@link MergePartnerSelectionDialogF} non-blocking, drive the candidate selection
 * via the combo box and the "select as merge partner" checkbox, and check the OK/Choose-All
 * enablement parity (Swing {@code checkApplicable}) plus the OK/cancel semantics;</li>
 * <li>open the {@link AbstractionPredicatesChoiceDialogF} (test-mode constructor) and check its
 * rendering and cancel semantics (the nested dialog of the predicate-abstraction merge
 * procedure);</li>
 * <li>log every assertion as a {@code ... PASS/FAIL} line and keep each dialog open for a few
 * seconds so screenshots can be taken (each dialog in turn).</li>
 * </ol>
 */
public final class JoinMergeVerifyF {

    private static final Logger LOGGER = LoggerFactory.getLogger(JoinMergeVerifyF.class);

    /** Strategy step limit for the preparation auto mode run (key.fx.verify.joinmerge.maxsteps). */
    private static final int MAX_STEPS = Integer
            .parseInt(System.getProperty("key.fx.verify.joinmerge.maxsteps", "40"));

    /** Seconds each dialog stays open for screenshots. */
    static final int SCREENSHOT_WINDOW_SECONDS = 14;

    private JoinMergeVerifyF() {
    }

    /**
     * Runs the self test. Must be called on the FX thread; the preparation auto mode runs on a
     * background thread and the dialog checks are marshalled back with {@link Platform#runLater}.
     *
     * @param owner the owner window for the dialogs (may be {@code null})
     * @param proof the loaded proof
     * @param proofControl the proof control (used for the preparation auto mode run and the menu
     *        item construction)
     * @return a short summary (the detailed report is logged)
     */
    public static String run(Window owner, Proof proof, ProofControl proofControl) {
        if (proof == null) {
            LOGGER.warn("JoinMerge verification: no proof loaded — SKIP");
            return "SKIP (no proof)";
        }
        Thread worker = new Thread(() -> {
            prepare(proof, proofControl);
            List<ProspectivePartner> partners = computeJoinPartners(proof);
            MergeAppData mergeApp = findMergeRuleApplication(proof);
            verifyForcedMergeCompletion(proof, mergeApp);
            Platform.runLater(() -> verifyJoinDialog(owner, proof, partners, () -> {
                verifyMergePartnerDialog(owner, proof, proofControl, mergeApp, () -> {
                    verifyAbstractionPredicatesDialog(owner, proof);
                });
            }));
        }, "fx-verify-joinmerge");
        worker.setDaemon(true);
        worker.start();
        return "running (see log)";
    }

    /**
     * Runs a limited auto mode on the given proof to create open branches (the dialogs need at
     * least two open goals; parity with the interactive scenario where the user stopped the auto
     * mode before the join/merge point).
     *
     * @param proof the proof
     * @param proofControl the proof control
     */
    private static void prepare(Proof proof, ProofControl proofControl) {
        try {
            proof.getSettings().getStrategySettings().setMaxSteps(MAX_STEPS);
            LOGGER.info("JoinMerge verification: preparation auto mode (max {} steps) started",
                MAX_STEPS);
            proofControl.startAndWaitForAutoMode(proof);
            LOGGER.info("JoinMerge verification: preparation auto mode finished ({} open goals)",
                proof.openGoals().size());
        } catch (RuntimeException e) {
            LOGGER.warn("JoinMerge verification: preparation auto mode failed: {}", e.toString());
        }
    }

    /**
     * Computes the join partners with the core call of the Swing context menu
     * ({@code JoinIsApplicable.INSTANCE.isApplicable}) over all open goals and their top-level
     * succedent formulas. Returns an empty list if none exist.
     *
     * @param proof the proof
     * @return the first non-empty partner list found
     */
    static List<ProspectivePartner> computeJoinPartners(Proof proof) {
        for (Goal goal : proof.openGoals()) {
            var succ = goal.sequent().succedent();
            for (int i = 0; i < succ.size(); i++) {
                PosInOccurrence pio =
                    new PosInOccurrence(succ.get(i), PosInTerm.getTopLevel(), false);
                try {
                    List<ProspectivePartner> partners =
                        JoinIsApplicable.INSTANCE.isApplicable(goal, pio);
                    if (!partners.isEmpty()) {
                        LOGGER.info(
                            "JoinMerge verification: {} real join partners for goal {}",
                            partners.size(), goal.node().serialNr());
                        return partners;
                    }
                } catch (RuntimeException e) {
                    LOGGER.debug("JoinMerge verification: applicability check failed", e);
                }
            }
        }
        return List.of();
    }

    /**
     * Builds a synthetic partner from the first two open leaf goals (fallback if no real join
     * partners exist; the dialog is then exercised for rendering/interaction, not for a real
     * join).
     *
     * @param proof the proof
     * @return a singleton list with the synthetic partner, or an empty list
     */
    static List<ProspectivePartner> syntheticPartner(Proof proof) {
        List<Goal> goals = new ArrayList<>();
        proof.openGoals().forEach(goals::add);
        if (goals.size() < 2) {
            return List.of();
        }
        Goal g1 = goals.get(0);
        Goal g2 = goals.get(1);
        Services services = proof.getServices();
        TermBuilder tb = services.getTermBuilder();

        SequentFormula sf1 = g1.sequent().succedent().get(0);
        SequentFormula sf2 = g2.sequent().succedent().get(0);
        JTerm referenceFormula = (JTerm) sf1.formula();
        JTerm update1 = tb.skip();
        if (referenceFormula.op() instanceof UpdateApplication) {
            update1 = referenceFormula.sub(0);
            referenceFormula = referenceFormula.sub(1);
        }
        JTerm update2 = tb.skip();
        JTerm formula2 = (JTerm) sf2.formula();
        if (formula2.op() instanceof UpdateApplication) {
            update2 = formula2.sub(0);
            formula2 = formula2.sub(1);
        }
        ProspectivePartner partner = new ProspectivePartner(referenceFormula, g1.node(), sf1,
            update1, g2.node(), sf2, update2);
        return List.of(partner);
    }

    /**
     * A merge rule application of admissible form with its potential merge partners, found by
     * scanning the open goals (the same information the Swing context menu action has available
     * when it is enabled).
     */
    private record MergeAppData(Goal goal, PosInOccurrence pio,
            ImmutableList<MergePartner> candidates) {
    }

    /**
     * Scans the open goals for a merge rule application of admissible form
     * ({@link MergeRule#isApplicable(Goal, PosInOccurrence)}) that has potential merge partners
     * ({@link MergeRule#findPotentialMergePartners}).
     *
     * @param proof the proof
     * @return the first suitable application found, or {@code null}
     */
    private static MergeAppData findMergeRuleApplication(Proof proof) {
        for (Goal goal : proof.openGoals()) {
            var sequent = goal.sequent();
            for (boolean inAntec : new boolean[] { false, true }) {
                var semi = inAntec ? sequent.antecedent() : sequent.succedent();
                for (int i = 0; i < semi.size(); i++) {
                    PosInOccurrence pio =
                        new PosInOccurrence(semi.get(i), PosInTerm.getTopLevel(), inAntec);
                    try {
                        if (!MergeRule.INSTANCE.isApplicable(goal, pio)) {
                            continue;
                        }
                        ImmutableList<MergePartner> candidates =
                            MergeRule.findPotentialMergePartners(goal, pio);
                        if (!candidates.isEmpty()) {
                            LOGGER.info(
                                "JoinMerge verification: {} merge candidates for goal {}",
                                candidates.size(), goal.node().serialNr());
                            return new MergeAppData(goal, pio, candidates);
                        }
                    } catch (RuntimeException e) {
                        LOGGER.debug("JoinMerge verification: merge applicability check failed",
                            e);
                    }
                }
            }
        }
        return null;
    }

    /**
     * Checks the <em>forced</em> (headless, no dialog) completion of the merge rule application
     * (Swing MergeRuleCompletion.complete forced mode: all potential partners and the
     * if-then-else merge method are chosen).
     *
     * @param proof the proof
     * @param mergeApp the merge application data (may be {@code null})
     */
    private static void verifyForcedMergeCompletion(Proof proof, MergeAppData mergeApp) {
        if (mergeApp == null) {
            LOGGER.info(
                "JoinMerge verification: merge-dialog SKIP (no admissible merge position with partners)");
            return;
        }
        try {
            MergeRuleBuiltInRuleApp app =
                (MergeRuleBuiltInRuleApp) MergeRule.INSTANCE.createApp(mergeApp.pio(),
                    proof.getServices());
            app.setMergeNode(mergeApp.goal().node());
            IBuiltInRuleApp completed = MergeRuleCompletionF.INSTANCE.complete(app,
                mergeApp.goal(), true);
            check("merge-completion forced completion returns an application", completed != null);
            if (completed instanceof MergeRuleBuiltInRuleApp mergeResult) {
                check("merge-completion forced completion selects all potential partners",
                    mergeResult.getMergePartners().size() == mergeApp.candidates().size());
                check("merge-completion forced completion chooses a concrete merge procedure",
                    mergeResult.getConcreteRule() != null);
            }
        } catch (RuntimeException e) {
            LOGGER.error("JoinMerge verification: forced merge completion threw", e);
            check("merge-completion forced completion runs without exception", false);
        }
    }

    /**
     * Opens the join dialog with the given partners (or the synthetic fallback) and runs the
     * assertions. Runs on the FX thread.
     *
     * @param owner the owner window
     * @param proof the proof
     * @param realPartners the real join partners (may be empty)
     */
    private static void verifyJoinDialog(Window owner, Proof proof,
            List<ProspectivePartner> realPartners, Runnable next) {
        boolean real = !realPartners.isEmpty();
        List<ProspectivePartner> partners = real ? realPartners : syntheticPartner(proof);
        if (partners.isEmpty()) {
            LOGGER.info("JoinMerge verification: join-dialog SKIP (fewer than two open goals)");
            next.run();
            return;
        }
        try {
            JoinDialogF dialog = new JoinDialogF(partners, proof, PredicateEstimator.STD_ESTIMATOR,
                proof.getServices(), owner);
            assertJoinDialog(dialog, proof, partners, real);
            assertOkCancelSemantics(proof, partners);
            LOGGER.info("JoinMerge verification: join dialog open for screenshot ({} s window)",
                SCREENSHOT_WINDOW_SECONDS);
            closeLater(dialog, SCREENSHOT_WINDOW_SECONDS, next);
        } catch (RuntimeException e) {
            LOGGER.error("JoinMerge verification: join-dialog FAIL (exception)", e);
            next.run();
        }
    }

    /**
     * Runs the join dialog assertions.
     *
     * @param dialog the dialog under test
     * @param proof the proof
     * @param partners the partners the dialog was constructed with
     * @param real whether the partners are real join partners (not synthetic)
     */
    private static void assertJoinDialog(JoinDialogF dialog, Proof proof,
            List<ProspectivePartner> partners, boolean real) {
        check("join-dialog dialog rendered", dialog.getStageForVerification() != null);
        check("join-dialog partner list has " + partners.size() + " entries",
            dialog.getChoiceList().getItems().size() == partners.size());

        var first = dialog.getChoiceList().getSelectionModel().getSelectedItem();
        check("join-dialog first partner preselected", first != null);
        if (first == null) {
            return;
        }
        check("join-dialog join-goal sequent rendered",
            !dialog.getSequentViewer2().getText().isEmpty());
        check("join-dialog predicate info label",
            first.getPredicateInfo().startsWith("Decision Formula"));
        check("join-dialog predicate input shows estimated predicate",
            dialog.getPredicateInput().getInput().equals(first.getPredicate(proof)));
        check("join-dialog info box shows a message",
            !dialog.getLastInfoMessage().getText().isEmpty());

        // OK enablement parity (Swing JoinDialog.java:43,132-141): valid input AND applicable
        // partner
        boolean expectedOk = first.isApplicable() && !first.getPredicate(proof).isEmpty();
        check("join-dialog OK " + (expectedOk ? "enabled" : "disabled") + " for first partner",
            dialog.getOkButton().isDisabled() != expectedOk);

        // selection change: the partner sequent view and the predicate input follow the choice
        if (partners.size() > 1) {
            String textBefore = dialog.getSequentViewer2().getText();
            dialog.getChoiceList().getSelectionModel().select(1);
            var second = dialog.getChoiceList().getSelectionModel().getSelectedItem();
            check("join-dialog selection changed to second partner",
                second != null && second != first);
            check("join-dialog partner sequent follows selection",
                !dialog.getSequentViewer2().getText().equals(textBefore)
                        || dialog.getSequentViewer2().getText()
                                .contains("Goal " + second.partner.getNode(1).serialNr()));
            check("join-dialog predicate input follows selection",
                dialog.getPredicateInput().getInput().equals(second.getPredicate(proof)));
            dialog.getChoiceList().getSelectionModel().selectFirst();
        }

        // invalid input disables the OK button (reason shown in the details box)
        DecisionPredicateInputF input = dialog.getPredicateInput();
        String validInput = input.getInput();
        input.setInput("&&&");
        check("join-dialog invalid formula disables OK", dialog.getOkButton().isDisabled());
        input.setInput(validInput);
        check("join-dialog restoring the formula re-enables/disables OK accordingly",
            dialog.getOkButton().isDisabled() != expectedOk);
    }

    /**
     * Runs the OK/cancel semantics assertions on a second (hidden) join dialog instance, so the
     * screenshot dialog stays open.
     *
     * @param proof the proof
     * @param partners the partners
     */
    private static void assertOkCancelSemantics(Proof proof, List<ProspectivePartner> partners) {
        JoinDialogF dialog = new JoinDialogF(partners, proof, PredicateEstimator.STD_ESTIMATOR,
            proof.getServices(), null);
        boolean okEnabled = !dialog.getOkButton().isDisabled();
        dialog.requestOk();
        check(
            "join-dialog OK press "
                + (okEnabled ? "confirms the dialog" : "ignored while disabled"),
            dialog.okButtonHasBeenPressed() == okEnabled);
        dialog.requestCancel();
        check("join-dialog cancel does not confirm", !dialog.okButtonHasBeenPressed());
        check("join-dialog cancel closes the dialog",
            !dialog.getStageForVerification().isShowing());
    }

    /**
     * Opens the merge partner selection dialog for the found merge application and runs the
     * assertions. Runs on the FX thread.
     *
     * @param owner the owner window
     * @param proof the proof
     * @param proofControl the proof control (used for the menu item construction check)
     * @param mergeApp the merge application data (may be {@code null})
     */
    private static void verifyMergePartnerDialog(Window owner, Proof proof,
            ProofControl proofControl, MergeAppData mergeApp, Runnable next) {
        if (mergeApp == null) {
            return; // SKIP already logged by verifyForcedMergeCompletion
        }
        try {
            MergePartnerSelectionDialogF dialog = new MergePartnerSelectionDialogF(mergeApp.goal(),
                mergeApp.pio(), mergeApp.candidates(), proof.getServices(), owner);
            dialog.showNonBlocking();
            assertMergePartnerDialog(dialog, proof, proofControl, mergeApp);
            LOGGER.info(
                "JoinMerge verification: merge partner dialog open for screenshot ({} s window)",
                SCREENSHOT_WINDOW_SECONDS);
            closeLater(dialog, SCREENSHOT_WINDOW_SECONDS, next);
        } catch (RuntimeException e) {
            LOGGER.error("JoinMerge verification: merge-dialog FAIL (exception)", e);
            next.run();
        }
    }

    /**
     * Runs the merge partner selection dialog assertions.
     *
     * @param dialog the dialog under test
     * @param proof the proof
     * @param proofControl the proof control
     * @param mergeApp the merge application data
     */
    private static void assertMergePartnerDialog(MergePartnerSelectionDialogF dialog, Proof proof,
            ProofControl proofControl, MergeAppData mergeApp) {
        check("merge-dialog dialog rendered", dialog.getStageForVerification() != null);
        check("merge-dialog candidate combo has " + mergeApp.candidates().size() + " entries",
            dialog.getCmbCandidates().getItems().size() == mergeApp.candidates().size());
        check("merge-dialog first candidate preselected",
            dialog.getCmbCandidates().getSelectionModel().getSelectedIndex() == 0);
        check("merge-dialog merge state sequent rendered",
            !dialog.getSequent1Flow().getChildren().isEmpty());
        check("merge-dialog partner sequent rendered",
            !dialog.getSequent2Flow().getChildren().isEmpty());
        check("merge-dialog OK disabled before a partner is chosen",
            dialog.getOkButton().isDisabled());
        check("merge-dialog distinguishing-formula field enabled iff single candidate",
            dialog.getTxtDistForm().isDisabled() != (mergeApp.candidates().size() == 1));

        // select the first candidate as merge partner (parity with the checkbox action)
        dialog.getCbSelectCandidate().fire();
        check("merge-dialog OK enabled after partner chosen", !dialog.getOkButton().isDisabled());

        // enablement parity (Swing checkApplicable)
        check("merge-dialog Choose-All " + "enablement parity",
            !dialog.getChooseAllButton().isDisabled());

        // OK/cancel semantics on a hidden second instance (so the screenshot dialog stays open)
        MergePartnerSelectionDialogF hidden =
            new MergePartnerSelectionDialogF(mergeApp.goal(), mergeApp.pio(),
                mergeApp.candidates(), proof.getServices(), null);
        hidden.getCbSelectCandidate().fire();
        hidden.requestOk();
        check("merge-dialog OK press keeps the chosen candidates",
            hidden.getChosenCandidates().size() == 1);
        hidden.requestCancel();
        check("merge-dialog cancel yields no chosen candidates",
            hidden.getChosenCandidates().isEmpty());

        // the menu item trigger exists and reads as in the Swing original
        MergeRuleMenuItemF item = new MergeRuleMenuItemF(mergeApp.goal(), mergeApp.pio(),
            proofControl);
        check("merge-dialog menu item is the State Merging Rule",
            "State Merging Rule".equals(item.getText()));
    }

    /**
     * Opens the abstraction-predicates choice dialog (the nested dialog of the
     * predicate-abstraction merge procedure) in test mode and checks its rendering and cancel
     * semantics. Runs on the FX thread.
     *
     * @param owner the owner window
     * @param proof the proof
     */
    private static void verifyAbstractionPredicatesDialog(Window owner, Proof proof) {
        try {
            AbstractionPredicatesChoiceDialogF dialog =
                new AbstractionPredicatesChoiceDialogF(proof.getServices(), owner);
            dialog.showNonBlocking();
            Stage stage = dialog.getStageForVerification();
            check("predabst-dialog dialog rendered", stage != null);
            if (stage != null) {
                check("predabst-dialog title",
                    stage.getTitle().startsWith("Choose abstraction predicates"));
                check("predabst-dialog content rendered", stage.getScene() != null
                        && stage.getScene().getRoot() != null);
            }
            LOGGER.info(
                "JoinMerge verification: abstraction predicates dialog open for screenshot ({} s window)",
                SCREENSHOT_WINDOW_SECONDS);
            closeLater(dialog, SCREENSHOT_WINDOW_SECONDS, null);
            // cancel semantics on a hidden instance (so the screenshot dialog stays open)
            AbstractionPredicatesChoiceDialogF hidden =
                new AbstractionPredicatesChoiceDialogF(proof.getServices(), null);
            hidden.requestCancel();
            check("predabst-dialog cancel reports no registered predicates",
                hidden.getResult().getRegisteredPredicates() == null);
        } catch (RuntimeException e) {
            LOGGER.error("JoinMerge verification: predabst-dialog FAIL (exception)", e);
        }
    }

    /**
     * Keeps the given dialog open for the screenshot window and then closes it on the FX thread;
     * afterwards the next verification step (if any) is run on the FX thread.
     *
     * @param dialog the dialog to close (must support {@code requestCancel})
     * @param seconds the window to keep the dialog open
     * @param next the next verification step (may be {@code null})
     */
    private static void closeLater(Object dialog, int seconds, Runnable next) {
        Thread closer = new Thread(() -> {
            try {
                Thread.sleep(seconds * 1000L);
            } catch (InterruptedException ignored) {
                Thread.currentThread().interrupt();
            }
            Platform.runLater(() -> {
                if (dialog instanceof JoinDialogF d) {
                    d.requestCancel();
                } else if (dialog instanceof MergePartnerSelectionDialogF d) {
                    d.requestCancel();
                } else if (dialog instanceof AbstractionPredicatesChoiceDialogF d) {
                    d.requestCancel();
                }
                if (next != null) {
                    next.run();
                }
            });
        }, "fx-verify-joinmerge-closer");
        closer.setDaemon(true);
        closer.start();
    }

    /**
     * Records one assertion result in the log.
     *
     * @param what the assertion description
     * @param condition the assertion condition
     */
    private static void check(String what, boolean condition) {
        LOGGER.info("JoinMerge verification: {} ... {}", what, condition ? "PASS" : "FAIL");
    }
}

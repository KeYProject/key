/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.tacletmatch;

import java.util.ArrayList;
import java.util.List;
import javafx.stage.Stage;

import de.uka.ilkd.key.control.AbstractProofControl;
import de.uka.ilkd.key.control.ProofControl;
import de.uka.ilkd.key.control.instantiation_model.TacletInstantiationModel;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.TacletApp;

import org.key_project.logic.PosInTerm;
import org.key_project.prover.proof.rulefilter.TacletFilter;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.util.collection.ImmutableList;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * The {@code key.fx.verify.tacletmatch} self test: after the demo proof load it programmatically
 * obtains an interactive (incomplete) taclet application on the current proof — the same flow the
 * Swing sequent-view term menu triggers via {@code AbstractProofControl.selectedTaclet}, which for
 * incomplete applications builds {@link TacletInstantiationModel}s and opens
 * {@link TacletMatchDialogF} (AbstractProofControl.java:226-258,
 * WindowUserInterfaceControl.completeAndApplyTacletMatch:330-338) — and asserts:
 * <ol>
 * <li>the dialog renders with the match highlighted (status line + schema-variable spans in the
 * matched term);</li>
 * <li>cancel closes the dialog and leaves the proof unchanged (node count stable);</li>
 * <li>apply closes the dialog and adds the application to the proof (node count changes).</li>
 * </ol>
 * Each assertion logs {@code PASS}/{@code FAIL} (and is surfaced as a toast by MainWindowF).
 *
 * <p>
 * The value of {@code key.fx.verify.tacletmatch} selects the mode: {@code 1} (default) runs the
 * full three-assertion flow; {@code hold} runs only the render assertion and leaves the dialog open
 * for interactive screenshots (light/dark theme checks).
 */
public final class TacletMatchVerifyF {

    private static final Logger LOGGER = LoggerFactory.getLogger(TacletMatchVerifyF.class);

    private TacletMatchVerifyF() {}

    /**
     * Runs the verification on the FX thread (called from the demo-load success handler in
     * MainWindowF).
     */
    public static void runTacletMatchVerification(Proof proof, ProofControl proofControl,
            Stage owner, NotationInfo notationInfo) {
        String mode = System.getProperty("key.fx.verify.tacletmatch", "1").trim();
        boolean hold = "hold".equalsIgnoreCase(mode);
        try {
            run(proof, proofControl, owner, notationInfo, hold);
        } catch (Throwable t) {
            LOGGER.error("tacletmatch verification: FAIL (unexpected error: {})", t, t);
        }
    }

    private static void run(Proof proof, ProofControl proofControl, Stage owner,
            NotationInfo notationInfo, boolean hold) {
        Services services = proof.getServices();
        Goal goal = proof.openEnabledGoals().head();
        AbstractProofControl control = (AbstractProofControl) proofControl;

        // ---- find an interactive (incomplete) taclet application on the current goal ----------
        TacletApp chosen = findIncompleteTacletApp(goal, services);
        if (chosen == null) {
            LOGGER.info(
                "tacletmatch verification: find-taclet-app: FAIL (no incomplete taclet "
                    + "application on the current goal)");
            return;
        }
        LOGGER.info("tacletmatch verification: find-taclet-app: PASS ({})", describe(chosen));

        int nodesBefore = proof.countNodes();

        // ---- assertion 1: the dialog renders with the highlighted match -----------------------
        TacletMatchDialogF renderDlg = openDialog(control, chosen, goal, owner, proofControl,
            services, notationInfo);
        boolean rendered = renderDlg.isShowing() && renderDlg.statusText() != null
                && !renderDlg.statusText().isBlank();
        LOGGER.info("tacletmatch verification: dialog-renders: {} (status \"{}\", showing={})",
            rendered ? "PASS" : "FAIL", renderDlg.statusText(), renderDlg.isShowing());

        int spans = renderDlg.highlightSpanCount(0);
        if (chosen.posInOccurrence() != null) {
            // find taclet: the matched term is expected to carry schema-variable highlights
            LOGGER.info(
                "tacletmatch verification: match-highlight: {} ({} schema-variable span(s) in "
                    + "the matched term)",
                spans > 0 ? "PASS" : "FAIL", spans);
        } else {
            LOGGER.info(
                "tacletmatch verification: match-highlight: PASS (no find pattern — the match "
                    + "overview renders the taclet without a matched term)");
        }

        if (hold) {
            // leave the dialog open for interactive screenshots (light/dark theme checks)
            LOGGER.info("tacletmatch verification: hold mode — dialog left open for screenshots");
            return;
        }

        // ---- assertion 2: cancel leaves the proof unchanged ----------------------------------
        int nodesAfterCancel = proof.countNodes();
        renderDlg.fireCancel();
        boolean cancelled =
            !renderDlg.isShowing() && proof.countNodes() == nodesAfterCancel;
        LOGGER.info("tacletmatch verification: cancel-keeps-proof: {} (node count before={}, "
            + "after={})", cancelled ? "PASS" : "FAIL", nodesBefore,
            proof.countNodes());

        // ---- assertion 3: apply closes the dialog and adds the application to the proof ------
        if (chosen.taclet().assumesSequent().isEmpty()) {
            // the schema-variable rows carry the model's pre-filled proposals, so the plain apply
            // flow (push input → createTacletApp → applyInteractive) completes the instantiation
            TacletMatchDialogF applyDlg = openDialog(control, chosen, goal, owner, proofControl,
                services, notationInfo);
            applyDlg.fireApply();
            boolean applied = !applyDlg.isShowing() && proof.countNodes() != nodesBefore;
            LOGGER.info("tacletmatch verification: apply-adds-to-proof: {} (node count before={}, "
                + "after={})", applied ? "PASS" : "FAIL", nodesBefore, proof.countNodes());
        } else {
            LOGGER.info(
                "tacletmatch verification: apply-adds-to-proof: SKIPPED (chosen taclet {} "
                    + "requires \\assumes instantiation, which needs typed user input)",
                chosen.taclet().name());
        }
    }

    private static TacletMatchDialogF openDialog(AbstractProofControl control, TacletApp app,
            Goal goal, Stage owner, ProofControl proofControl, Services services,
            NotationInfo notationInfo) {
        TacletInstantiationModel[] models = control.completeAndApplyApp(List.of(app), goal);
        return new TacletMatchDialogF(owner, models, goal, proofControl, services, notationInfo);
    }

    /**
     * finds a taclet application on the given goal whose instantiation is incomplete (the condition
     * under which the Swing term menu routes to the instantiation dialog,
     * AbstractProofControl.java:226-258) and that the dialog can complete without typed user
     * input: the models pre-fill a proposal for every remaining (skolem/variable) schema variable
     * (TacletFindModel.java:121-138), so an application with {@code completeExceptSkolemConstants
     * () == false} still has unproposable (formula) inputs and would fail the apply step.
     * Preferences, in order: a find-taclet app with a match position, no {@code \assumes} and only
     * proposable inputs left (exercises the match highlighting and the plain apply flow — e.g. an
     * {@code \existsRight} skolem constant), then any find-taclet app without {@code \assumes},
     * then any app without {@code \assumes}, then any incomplete app.
     */
    private static TacletApp findIncompleteTacletApp(Goal goal, Services services) {
        List<TacletApp> candidates = new ArrayList<>();
        ImmutableList<de.uka.ilkd.key.rule.NoPosTacletApp> noFind =
            goal.ruleAppIndex().getNoFindTaclet(TacletFilter.TRUE, services);
        noFind.forEach(candidates::add);
        org.key_project.prover.sequent.Sequent seq = goal.sequent();
        for (int i = 1; i <= seq.size(); i++) {
            PosInOccurrence pio = PosInOccurrence.findInSequent(seq, i, PosInTerm.getTopLevel());
            ImmutableList<TacletApp> apps =
                goal.ruleAppIndex().getTacletAppAtAndBelow(TacletFilter.TRUE, pio, services);
            apps.forEach(candidates::add);
        }

        TacletApp findProposable = null;
        TacletApp findWithoutAssumes = null;
        TacletApp withoutAssumes = null;
        TacletApp any = null;
        for (TacletApp app : candidates) {
            if (app.complete()) {
                continue;
            }
            boolean proposable = app.completeExceptSkolemConstants();
            boolean hasAssumes = !app.taclet().assumesSequent().isEmpty();
            if (app.posInOccurrence() != null && !hasAssumes) {
                if (proposable && findProposable == null) {
                    findProposable = app;
                }
                if (findWithoutAssumes == null) {
                    findWithoutAssumes = app;
                }
            }
            if (proposable && !hasAssumes && withoutAssumes == null) {
                withoutAssumes = app;
            }
            if (any == null) {
                any = app;
            }
        }
        return findProposable != null ? findProposable
                : findWithoutAssumes != null ? findWithoutAssumes
                        : withoutAssumes != null ? withoutAssumes : any;
    }

    /** a short human-readable description of the chosen application for the log line */
    private static String describe(TacletApp app) {
        PosInOccurrence pio = app.posInOccurrence();
        return app.taclet().name() + " at "
            + (pio == null ? "no position" : (pio.isInAntec() ? "antecedent" : "succedent"));
    }
}

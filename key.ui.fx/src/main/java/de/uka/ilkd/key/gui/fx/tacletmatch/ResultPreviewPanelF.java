/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.tacletmatch;

import java.util.ArrayList;
import java.util.List;
import javafx.animation.PauseTransition;
import javafx.geometry.Insets;
import javafx.geometry.Pos;
import javafx.scene.Node;
import javafx.scene.control.Button;
import javafx.scene.control.Label;
import javafx.scene.control.Separator;
import javafx.scene.layout.HBox;
import javafx.scene.layout.Priority;
import javafx.scene.layout.VBox;
import javafx.util.Duration;

import de.uka.ilkd.key.control.instantiation_model.TacletInstantiationModel;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.executor.javadl.TacletExecutor;

import org.key_project.prover.sequent.FormulaChangeInfo;
import org.key_project.prover.sequent.Sequent;
import org.key_project.prover.sequent.SequentChangeInfo;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.util.collection.ImmutableList;

/**
 * Shows the sequent(s) that applying the taclet with the current instantiations would produce. The
 * result is computed with the executor's side-effect-free
 * {@link TacletExecutor#getResultSequentChanges} (never {@code Goal.apply}), so it does not touch
 * the proof. It refreshes, debounced, whenever the instantiations change; while they are incomplete
 * it shows a hint instead.
 *
 * <p>
 * Port of {@code de.uka.ilkd.key.gui.tacletmatch.ResultPreviewPanel} (ResultPreviewPanel.java:
 * 29-236): the never-mutate contract of ResultPreviewPanel.java:23-25 is kept verbatim; the Swing
 * 150&nbsp;ms debounce {@code Timer} becomes a {@link PauseTransition} (ResultPreviewPanel.java:
 * 63-70); the added/removed/modified rows with {@code +}/{@code −} markers and the expandable full
 * sequent are re-laid out with labels and {@link ExpandableTextF}s.
 */
class ResultPreviewPanelF extends VBox {

    /** debounce of the preview refresh (ResultPreviewPanel.java:38) */
    private static final Duration PREVIEW_DEBOUNCE = Duration.millis(150);

    private final TacletInstantiationModel model;
    private final Services services;
    private final NotationInfo notationInfo;
    private final Goal goal;

    private final VBox body = new VBox(4);
    private PauseTransition debounce;

    ResultPreviewPanelF(TacletInstantiationModel model, Services services,
            NotationInfo notationInfo, Goal goal) {
        this.model = model;
        this.services = services;
        this.notationInfo = notationInfo;
        this.goal = goal;

        // the resulting sequent sits on a surface card (the "answer") — Swing used the editor
        // background with a hairline border (ResultPreviewPanel.java:48-57)
        body.getStyleClass().add("tacletmatch-preview-card");
        VBox section = TmStyleF.section("Result preview", body);
        getChildren().add(section);

        update();
    }

    /** schedules a debounced refresh of the preview (ResultPreviewPanel.java:63-70). */
    public void requestUpdate() {
        if (debounce == null) {
            debounce = new PauseTransition(PREVIEW_DEBOUNCE);
            debounce.setOnFinished(e -> update());
        }
        debounce.playFromStart();
    }

    /**
     * recomputes and renders the preview from the current instantiations (ResultPreviewPanel.java:
     * 72-94).
     */
    public void update() {
        body.getChildren().clear();
        try {
            TacletApp app = model.createTacletApp();
            if (app == null) {
                message("Could not apply the rule with the current instantiations.");
            } else {
                TacletExecutor exec = (TacletExecutor) app.taclet().getExecutor();
                ImmutableList<SequentChangeInfo> changes =
                    exec.getResultSequentChanges(goal, app);
                if (changes.isEmpty()) {
                    message("No preview available for this rule.");
                } else {
                    renderGoals(changes);
                }
            }
        } catch (Exception e) {
            message("Complete the instantiations to preview the result.");
        }
    }

    private void renderGoals(ImmutableList<SequentChangeInfo> changes) {
        int n = changes.size();
        int i = 1;
        for (SequentChangeInfo sci : changes) {
            if (i > 1) {
                // a visible divider between resulting goals
                body.getChildren().add(new Separator());
            }

            VBox goalBox = new VBox(2);
            goalBox.setPadding(new Insets(2, 0, 2, 0));

            ExpandableTextF full =
                new ExpandableTextF(printSequent(sci.sequent()), Integer.MAX_VALUE);
            full.setVisible(false);
            full.setManaged(false);
            Button toggle = expandToggle(full);

            if (n > 1) {
                // multiple goals: a header line carries the "Goal i of n" label and the toggle
                HBox header = new HBox(8);
                header.setAlignment(Pos.CENTER_LEFT);
                Label l = TmStyleF.muted("Goal " + i + " of " + n);
                HBox.setHgrow(l, Priority.ALWAYS);
                header.getChildren().addAll(l, toggle);
                goalBox.getChildren().add(header);
            } else {
                // single goal: put the toggle on its own small row at the top of the card
                HBox header = new HBox(8);
                header.setAlignment(Pos.CENTER_RIGHT);
                header.getChildren().add(toggle);
                goalBox.getChildren().add(header);
            }

            goalBox.getChildren().addAll(renderSide(sci, true).toArray(Node[]::new));
            goalBox.getChildren().addAll(renderSide(sci, false).toArray(Node[]::new));

            goalBox.getChildren().add(full);
            body.getChildren().add(goalBox);
            i++;
        }
    }

    /**
     * a small, unobtrusive button that toggles the full-sequent view (ResultPreviewPanel.java:
     * 158-169).
     */
    private Button expandToggle(ExpandableTextF full) {
        Button b = TmStyleF.disclosure("the full sequent");
        b.setOnAction(e -> {
            boolean show = !full.isVisible();
            full.setVisible(show);
            full.setManaged(show);
            TmStyleF.setDisclosure(b, show);
        });
        return b;
    }

    /**
     * renders the added/removed/modified formulas of one side (ResultPreviewPanel.java:172-193).
     */
    private List<Node> renderSide(SequentChangeInfo sci, boolean antec) {
        ImmutableList<SequentFormula> removed = sci.removedFormulas(antec);
        ImmutableList<SequentFormula> added = sci.addedFormulas(antec);
        ImmutableList<FormulaChangeInfo> modified = sci.modifiedFormulas(antec);

        List<Node> out = new ArrayList<>();
        if (removed.isEmpty() && added.isEmpty() && modified.isEmpty()) {
            return out;
        }
        Label head = TmStyleF.muted(antec ? "antecedent" : "succedent");
        out.add(head);
        for (SequentFormula f : removed) {
            out.add(changeRow("−", false, f));
        }
        for (FormulaChangeInfo m : modified) {
            out.add(changeRow("−", false, m.getOriginalFormula()));
            out.add(changeRow("+", true, m.newFormula()));
        }
        for (SequentFormula f : added) {
            out.add(changeRow("+", true, f));
        }
        return out;
    }

    private Node changeRow(String marker, boolean added, SequentFormula f) {
        Label m = new Label(marker);
        m.getStyleClass().add(added ? "tacletmatch-added" : "tacletmatch-removed");
        m.setPadding(new Insets(0, 8, 0, 0));

        ExpandableTextF text = new ExpandableTextF(TmPrintF.term(services, notationInfo,
            f.formula()));
        HBox p = new HBox(6, m, text);
        p.setAlignment(Pos.CENTER_LEFT);
        HBox.setHgrow(text, Priority.ALWAYS);
        return p;
    }

    private void message(String text) {
        Label l = TmStyleF.muted(text);
        l.setWrapText(true);
        body.getChildren().add(l);
    }

    private String printSequent(Sequent seq) {
        StringBuilder sb = new StringBuilder();
        for (SequentFormula sf : seq.antecedent()) {
            sb.append(TmPrintF.term(services, notationInfo, sf.formula())).append('\n');
        }
        sb.append("⟹");
        for (SequentFormula sf : seq.succedent()) {
            sb.append('\n').append(TmPrintF.term(services, notationInfo, sf.formula()));
        }
        return sb.toString();
    }
}

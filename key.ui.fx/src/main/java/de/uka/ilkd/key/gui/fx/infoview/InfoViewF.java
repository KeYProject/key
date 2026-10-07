/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.infoview;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.Objects;
import java.util.stream.Collectors;
import javafx.geometry.Insets;
import javafx.scene.control.Label;
import javafx.scene.control.ScrollPane;
import javafx.scene.layout.GridPane;
import javafx.scene.layout.VBox;

import de.uka.ilkd.key.core.fx.KeYSelectionEvent;
import de.uka.ilkd.key.core.fx.KeYSelectionListener;
import de.uka.ilkd.key.core.fx.KeYSelectionModel;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;

import org.key_project.util.javafx.FxUtil;

/**
 * First JavaFX version of the info view, the counter-part of
 * {@code de.uka.ilkd.key.gui.InfoView} (a Swing {@code JSplitPane} with a rule/symbol browser
 * tree) in the module {@code key.ui}.
 * <p>
 * <b>Milestone M2, first version.</b> This version shows the essential details of the selected
 * proof as a table of labeled rows (proof file, goal and node statistics, closed status), which
 * the Swing UI displays in the statistics dialog
 * ({@code de.uka.ilkd.key.gui.actions.ShowProofStatistics}) and in the loading report of
 * {@code de.uka.ilkd.key.proof.io.ProblemLoader} ({@code countNodes()},
 * {@code countBranches() - openGoals().size()}). The statistics are recomputed on every
 * {@code selectedProofChanged} notification; the data comes directly from the {@link Proof}
 * (no mediator):
 * <ul>
 * <li>proof file: {@link Proof#getProofFile()} (the path of the loaded problem, may be
 * {@code null} for programmatically created proofs),</li>
 * <li>open goals: {@link Proof#openGoals()}.size(),</li>
 * <li>closed goals: {@link Proof#countBranches()} minus the open goals — the formula the Swing
 * loading report uses ({@code ProblemLoader.fireTaskFinished}); {@link Proof#closedGoals()} is
 * deliberately not used, because it stays empty by default
 * ({@code GeneralSettings.noPruningClosed = true}),</li>
 * <li>total nodes: single pass over {@link Node#subtreeIterator()} from {@link Proof#root()},</li>
 * <li>branches: number of nodes with {@link Node#childrenCount()} &gt; 1 (branch points; note
 * that {@link Proof#countBranches()} returns the number of leaves instead),</li>
 * <li>status: {@link Proof#closed()}.</li>
 * </ul>
 * <p>
 * Deliberately deferred to later milestones: the rule/symbol/choice browser of the Swing
 * {@code InfoNodeFactory}, node-level details, live refresh while the prover applies rules, and
 * background computation of the statistics (currently a synchronous tree walk on the FX thread,
 * which is fine for small demo proofs).
 * <p>
 * Style classes (see {@code key-light.css}/{@code key-dark.css}, section "info view"):
 * {@code .info-view} (this scroll pane), {@code .info-view-content}, {@code .info-view-title},
 * {@code .info-view-grid}, {@code .info-row-label}, {@code .info-row-value},
 * {@code .info-view-status-closed}, {@code .info-view-status-open},
 * {@code .info-view-placeholder}.
 */
public class InfoViewF extends ScrollPane {

    /** One labeled row of the info table. */
    private record Row(String key, Label label, Label value) {
    }

    private final VBox content = new VBox();
    private final Label title = new Label();
    private final GridPane grid = new GridPane();
    private final Label placeholder = new Label("No proof selected.");
    private final List<Row> rows = new ArrayList<>();

    private Label fileValue;
    private Label openGoalsValue;
    private Label closedGoalsValue;
    private Label nodesValue;
    private Label branchesValue;
    private Label statusValue;

    private KeYSelectionModel selectionModel;
    private Proof proof;
    /** number of proof nodes rendered in the nodes row (for {@link #verifyInfoView()}) */
    private int nodeCount;
    /** number of branch points rendered in the branches row (for {@link #verifyInfoView()}) */
    private int branchCount;

    private final KeYSelectionListener selectionListener = new KeYSelectionListener() {
        @Override
        public void selectedProofChanged(KeYSelectionEvent<Proof> event) {
            display(event.getSource().getSelectedProof());
        }
    };

    /**
     * Creates an empty info view.
     */
    public InfoViewF() {
        getStyleClass().add("info-view");
        setFitToWidth(true);

        content.getStyleClass().add("info-view-content");
        content.setPadding(new Insets(8));

        title.getStyleClass().add("info-view-title");

        grid.getStyleClass().add("info-view-grid");
        grid.setHgap(10);
        grid.setVgap(4);

        fileValue = addRow("Proof File");
        openGoalsValue = addRow("Open Goals");
        closedGoalsValue = addRow("Closed Goals");
        nodesValue = addRow("Nodes");
        branchesValue = addRow("Branches");
        statusValue = addRow("Status");

        placeholder.getStyleClass().add("info-view-placeholder");

        content.getChildren().addAll(title, grid, placeholder);
        setContent(content);
        showPlaceholder();
    }

    /**
     * Appends a labeled row to the grid.
     *
     * @param key the row's key (used by the self test to report empty fields)
     * @return the value label of the created row
     */
    private Label addRow(String key) {
        Label label = new Label(key);
        label.getStyleClass().add("info-row-label");
        Label value = new Label();
        value.getStyleClass().add("info-row-value");
        int rowIndex = grid.getRowCount();
        grid.add(label, 0, rowIndex);
        grid.add(value, 1, rowIndex);
        rows.add(new Row(key, label, value));
        return value;
    }

    /**
     * Registers this view as a selection listener on the given model and displays the currently
     * selected proof, if any. Only {@code selectedProofChanged} is observed; this version is
     * proof-level and shows no node details.
     *
     * @param model the selection model to observe
     */
    public void attach(KeYSelectionModel model) {
        Objects.requireNonNull(model);
        if (selectionModel == model) {
            return;
        }
        if (selectionModel != null) {
            selectionModel.removeKeYSelectionListener(selectionListener);
        }
        selectionModel = model;
        model.addKeYSelectionListenerChecked(selectionListener);
        display(model.getSelectedProof());
    }

    /**
     * Displays the details of the given proof.
     *
     * @param newProof the proof to display, may be {@code null} to clear the view
     */
    public void display(Proof newProof) {
        if (!FxUtil.isFxThread()) {
            FxUtil.runLater(() -> display(newProof));
            return;
        }
        proof = newProof;
        if (proof == null) {
            showPlaceholder();
            return;
        }
        showTable();
        title.setText(proof.name().toString());
        fileValue.setText(proof.getProofFile() != null ? proof.getProofFile().toString() : "-");
        openGoalsValue.setText(Integer.toString(proof.openGoals().size()));
        // "closed goals" as reported by the Swing loading report: leaves minus open goals
        // (Proof.closedGoals() stays empty by default, GeneralSettings.noPruningClosed = true)
        closedGoalsValue
                .setText(Integer.toString(proof.countBranches() - proof.openGoals().size()));
        nodeCount = 0;
        branchCount = 0;
        for (Iterator<Node> it = proof.root().subtreeIterator(); it.hasNext();) {
            Node node = it.next();
            nodeCount++;
            if (node.childrenCount() > 1) {
                branchCount++;
            }
        }
        nodesValue.setText(Integer.toString(nodeCount));
        branchesValue.setText(Integer.toString(branchCount));
        boolean closed = proof.closed();
        statusValue.setText(closed ? "closed" : "open");
        statusValue.getStyleClass().removeIf(c -> c.startsWith("info-view-status-"));
        statusValue.getStyleClass()
                .add(closed ? "info-view-status-closed" : "info-view-status-open");
    }

    /**
     * @return the displayed proof, or {@code null} if none is selected
     */
    public Proof getProof() {
        return proof;
    }

    private void showTable() {
        title.setManaged(true);
        title.setVisible(true);
        grid.setManaged(true);
        grid.setVisible(true);
        placeholder.setManaged(false);
        placeholder.setVisible(false);
    }

    private void showPlaceholder() {
        title.setText("");
        title.setManaged(false);
        title.setVisible(false);
        grid.setManaged(false);
        grid.setVisible(false);
        placeholder.setManaged(true);
        placeholder.setVisible(true);
    }

    /**
     * Development self-test (M2): verifies that the info view is completely populated for the
     * displayed proof and that the rendered node count matches a fresh traversal of
     * {@code proof.root().subtreeIterator()}. May be called from any thread.
     *
     * @return a one-line report, {@code "... PASS"} if all fields are non-empty and the node
     *         counts agree
     */
    public String verifyInfoView() {
        if (!FxUtil.isFxThread()) {
            return FxUtil.callAndWait(this::verifyInfoView);
        }
        if (proof == null) {
            return "no proof selected FAIL";
        }
        int independentNodeCount = 0;
        for (Iterator<Node> it = proof.root().subtreeIterator(); it.hasNext();) {
            it.next();
            independentNodeCount++;
        }
        String emptyFields = rows.stream()
                .filter(row -> row.value().getText() == null || row.value().getText().isBlank())
                .map(Row::key)
                .collect(Collectors.joining(","));
        boolean pass = emptyFields.isEmpty() && !title.getText().isBlank()
                && nodeCount == independentNodeCount
                && Integer.toString(independentNodeCount).equals(nodesValue.getText());
        return "proof=" + proof.name() + " openGoals=" + openGoalsValue.getText()
            + " closedGoals=" + closedGoalsValue.getText() + " nodes=" + nodesValue.getText()
            + " independentNodes=" + independentNodeCount + " branches=" + branchesValue.getText()
            + " status=" + statusValue.getText()
            + (emptyFields.isEmpty() ? "" : " emptyFields=" + emptyFields)
            + " " + (pass ? "PASS" : "FAIL");
    }
}

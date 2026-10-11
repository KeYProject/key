/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2,
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.plugins.caching.fx;

import java.util.Collections;
import java.util.List;
import java.util.stream.Collectors;
import javafx.beans.property.ReadOnlyStringWrapper;
import javafx.collections.FXCollections;
import javafx.geometry.Insets;
import javafx.geometry.Pos;
import javafx.scene.Scene;
import javafx.scene.control.Button;
import javafx.scene.control.Label;
import javafx.scene.control.ProgressBar;
import javafx.scene.control.ScrollPane;
import javafx.scene.control.TableColumn;
import javafx.scene.control.TableView;
import javafx.scene.control.Tooltip;
import javafx.scene.layout.BorderPane;
import javafx.scene.layout.HBox;
import javafx.scene.layout.Priority;
import javafx.scene.layout.Region;
import javafx.stage.Modality;
import javafx.stage.Stage;
import javafx.stage.Window;

import de.uka.ilkd.key.core.fx.KeYMediatorF;
import de.uka.ilkd.key.gui.fx.IssueDialogF;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.reference.ClosedBy;

import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Dialog showing the results of the reference search, FX port of {@code ReferenceSearchDialog} +
 * {@code ReferenceSearchTable} (Swing ReferenceSearchDialog.java:25-171,
 * ReferenceSearchTable.java:26-123): the per-goal table lists every open goal of the proof (and
 * every goal closed by reference) with the found reference, a progress bar tracks the
 * "Apply" copy (Swing paints the status string on the bar; the FX port shows it as a label
 * next to the bar), and the Close / Apply button row closes the dialog or applies the results
 * (i.e. copies the referenced steps into the current proof, done by the
 * {@link ReferenceSearchDialogListenerF} — Swing {@code DefaultReferenceSearchDialogListener}).
 * <p>
 * The table is a snapshot built at construction time (Swing parity: the Swing table model keeps
 * the goal list it was built with), the "Reference" column is resolved live through the
 * mediator's opened proofs (Swing ReferenceSearchTable.java:102-105).
 */
final class ReferenceSearchDialogF {
    private static final Logger LOGGER = LoggerFactory.getLogger(ReferenceSearchDialogF.class);

    /** The open (and referenced) goals of the proof — the rows of the table. */
    private final List<Goal> goals;

    /** the mediator (the "Reference" column resolves the proof index in the opened proofs) */
    private final @Nullable KeYMediatorF mediator;

    /** the listener reacting to the Close / Apply buttons */
    private final ReferenceSearchDialogListenerF listener;

    private final ProgressBar progressBar = new ProgressBar(1);
    private final Label progressLabel = new Label("Finished.");
    private final Button applyButton = new Button("Apply");
    private final Button closeButton = new Button("Close");

    /** overall progress of the copy (Swing JProgressBar, maximum 1 = "Finished.") */
    private int progressMaximum = 1;
    private int progressValue = 1;

    private Stage stage;

    /**
     * Construct a new dialog. Use {@link #show()} afterwards to show it.
     *
     * @param owner the owner window, may be {@code null}
     * @param proof the proof to analyze
     * @param mediator the mediator, may be {@code null} (the reference column then reports the
     *        fallback index 0, like Swing when the proof is not among the opened proofs)
     * @param listener control listener
     */
    ReferenceSearchDialogF(@Nullable Window owner, Proof proof, @Nullable KeYMediatorF mediator,
            ReferenceSearchDialogListenerF listener) {
        this.mediator = mediator;
        this.listener = listener;

        // Swing ReferenceSearchTable ctor (ReferenceSearchTable.java:44-47): the open goals plus
        // the goals closed by reference, in reverse order
        goals = proof.allGoals().stream()
                .filter(g -> !g.node().isClosed() || g.node().lookup(ClosedBy.class) != null)
                .collect(Collectors.toList());
        Collections.reverse(goals);

        TableColumn<Goal, String> goalColumn = new TableColumn<>("Goal");
        goalColumn.setCellValueFactory(
            data -> new ReadOnlyStringWrapper(
                String.valueOf(data.getValue().node().serialNr())));
        TableColumn<Goal, String> referenceColumn = new TableColumn<>("Reference");
        referenceColumn.setCellValueFactory(
            data -> new ReadOnlyStringWrapper(referenceText(data.getValue())));
        // Swing ReferenceSearchTable ctor: the reference column is the wide one
        referenceColumn.setMinWidth(200);
        TableView<Goal> table = new TableView<>(FXCollections
                .observableList(goals));
        table.getColumns().add(goalColumn);
        table.getColumns().add(referenceColumn);
        table.setColumnResizePolicy(TableView.CONSTRAINED_RESIZE_POLICY_FLEX_LAST_COLUMN);
        table.setEditable(false);
        // Swing JTable default: rows are not selectable/editable data entry (the dialog's
        // interaction happens through the buttons); keep the plain look
        table.getColumns().forEach(c -> c.setSortable(false));

        ScrollPane scroll = new ScrollPane(table);
        scroll.setFitToWidth(true);
        scroll.setFitToHeight(true);

        HBox top = new HBox(8, progressBar, progressLabel);
        top.setAlignment(Pos.CENTER_LEFT);
        top.setPadding(new Insets(5, 5, 0, 5));
        progressBar.setMaxWidth(Double.MAX_VALUE);
        HBox.setHgrow(progressBar, Priority.ALWAYS);

        applyButton.setTooltip(new Tooltip("Apply the results (i.e. copy steps into current "
            + "proof)"));
        applyButton.setDisable(true);
        applyButton.setOnAction(e -> {
            try {
                applyButton.setDisable(true);
                closeButton.setDisable(true);
                listener.copyButtonClicked(this);
            } catch (Exception exception) {
                // There may be exceptions during rule application that should not be lost.
                LOGGER.error("", exception);
                IssueDialogF.showExceptionDialog(stage, exception);
            }
        });
        closeButton.setOnAction(e -> listener.closeButtonClicked(this));
        // Swing ReferenceSearchDialog ctor (ReferenceSearchDialog.java:98-100): apply is only
        // enabled when the proof has goals closed by reference
        if (proof.closedGoals().stream().anyMatch(g -> g.node().lookup(ClosedBy.class) != null)) {
            applyButton.setDisable(false);
        }

        Region spacer = new Region();
        HBox.setHgrow(spacer, Priority.ALWAYS);
        HBox buttonBar = new HBox(5, spacer, closeButton, applyButton);
        buttonBar.setPadding(new Insets(5, 5, 5, 5));

        BorderPane root = new BorderPane();
        root.setTop(top);
        root.setCenter(scroll);
        root.setBottom(buttonBar);

        stage = new Stage();
        if (owner != null) {
            stage.initOwner(owner);
        }
        stage.initModality(Modality.APPLICATION_MODAL);
        stage.setTitle("Proof Caching");
        stage.setScene(new Scene(root, 520, 360));
    }

    /** Shows the dialog (non-blocking; the Swing dialog blocks via {@code setVisible(true)}). */
    void show() {
        stage.show();
    }

    /** Closes the dialog (Swing {@code dispose}). */
    void close() {
        if (stage != null) {
            stage.close();
        }
    }

    /**
     * Perform the "Apply" action programmatically (Swing {@code apply}:
     * {@code getApplyButton().doClick()}).
     */
    void apply() {
        applyButton.fire();
    }

    /**
     * Set the maximum value of the progress bar. Also resets progress to zero (Swing
     * {@code setMaximum}).
     *
     * @param total total value
     */
    void setMaximum(int total) {
        progressMaximum = total;
        progressValue = 0;
        progressBar.setProgress(0);
        progressLabel.setText("Working...");
    }

    /**
     * Increment progress by one (Swing {@code incrementProgress}).
     *
     * @return whether progress is full
     */
    boolean incrementProgress() {
        progressValue++;
        progressBar.setProgress(progressMaximum <= 0 ? 1 : (double) progressValue / progressMaximum);
        if (progressValue == progressMaximum) {
            progressLabel.setText("Finished.");
            return true;
        }
        return false;
    }

    // ------------------------------------------------------------------
    // verify harness seams (key.fx.verify.caching, see CachingVerifyF)
    // ------------------------------------------------------------------

    boolean isShowing() {
        return stage != null && stage.isShowing();
    }

    /** @return the number of table rows (the filtered goal snapshot) */
    int rowCount() {
        return goals.size();
    }

    /**
     * Swing {@code ReferenceSearchTable.getValueAt}: column 0 is the goal's node serial number,
     * column 1 the reference text.
     */
    String cellText(int row, int column) {
        Goal goal = goals.get(row);
        if (column == 0) {
            return String.valueOf(goal.node().serialNr());
        }
        return referenceText(goal);
    }

    boolean isApplyEnabled() {
        return !applyButton.isDisable();
    }

    boolean isCloseEnabled() {
        return !closeButton.isDisable();
    }

    String progressText() {
        return progressLabel.getText();
    }

    /**
     * Swing {@code ReferenceSearchTable.getValueAt} column 1: the reference description of the
     * goal ("no reference found", or the 1-based index of the referenced proof among the
     * currently opened proofs plus the referenced node's serial number).
     */
    private String referenceText(Goal goal) {
        ClosedBy c = goal.node().lookup(ClosedBy.class);
        if (c == null) {
            return "no reference found";
        }
        KeYMediatorF m = mediator;
        int i = m == null ? 0 : m.getCurrentlyOpenedProofs().indexOf(c.proof()) + 1;
        return String.format("reference available (proof %d, node %d)", i, c.node().serialNr());
    }
}

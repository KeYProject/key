/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.isabelletranslation.fx;

import java.util.ArrayList;
import java.util.List;
import javafx.geometry.Insets;
import javafx.geometry.Pos;
import javafx.scene.Scene;
import javafx.scene.control.Button;
import javafx.scene.control.Label;
import javafx.scene.control.ProgressBar;
import javafx.scene.control.ScrollPane;
import javafx.scene.control.Tooltip;
import javafx.scene.layout.BorderPane;
import javafx.scene.layout.ColumnConstraints;
import javafx.scene.layout.GridPane;
import javafx.scene.layout.HBox;
import javafx.scene.layout.Priority;
import javafx.scene.layout.Region;
import javafx.scene.paint.Color;
import javafx.stage.Modality;
import javafx.stage.Stage;
import javafx.stage.Window;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * Dialog showing the launched Isabelle solver processes and their results, JavaFX port of the
 * Swing {@code org.key_project.isabelletranslation.gui.IsabelleProgressDialog} +
 * {@code IsabelleProgressModel} (IsabelleProgressDialog.java:44-469, IsabelleProgressModel.java):
 * an overall progress bar ("Processed X of N problems."), one row per solver with its goal name,
 * a per-solver progress bar, a status text (green valid / red exception / blue unknown, the
 * Swing {@code ColorSettings} constants) and an Info button, plus the Stop/Apply button row
 * (Stop becomes Discard once the solvers are done, Swing {@code IsabelleProgressDialog.Modus}).
 * <p>
 * Swing renders the per-solver progress as a table cell editor; here the same two-column layout
 * (goal name column, progress column) is a plain {@link GridPane} — the mediator drives the
 * widgets directly instead of through a table model.
 */
@NullMarked
final class IsabelleSolverProgressDialogF {

    /**
     * Resolution of the per-solver progress bars (Swing IsabelleLauncherProgressDialogMediator
     * RESOLUTION / IsabelleProgressDialog.ProgressPanel).
     */
    static final int RESOLUTION = 1000;

    /** The green valid colour (Swing ColorSettings "[isabelleDialog]green", 43,180,43). */
    static final Color GREEN = Color.rgb(43, 180, 43);
    /** The red exception colour (Swing ColorSettings "[isabelleDialog]red", 180,43,43). */
    static final Color RED = Color.rgb(180, 43, 43);
    /** The colour of the unknown stop reason (Swing mediator unknownStopped: Color.BLUE). */
    static final Color UNKNOWN = Color.BLUE;

    /** Current state of the dialog (Swing {@code IsabelleProgressDialog.Modus}). */
    enum Modus {
        /** Isabelle solvers are running and may be stopped by the user. */
        SOLVERS_RUNNING,
        /** Isabelle solvers are done (or terminated). Results may be applied by the user. */
        SOLVERS_DONE
    }

    /**
     * Listener interface to interact with this dialog, used for the stop, apply, discard and info
     * buttons (Swing {@code IsabelleProgressDialog.IsabelleProgressDialogListener}).
     */
    interface Listener {
        /**
         * The info button of the solver row {@code row} was clicked (Swing
         * {@code infoButtonClicked(column, row)}; the FX port has exactly one solver column, so
         * the column index is dropped).
         */
        void infoButtonClicked(int row);

        /** The stop button was clicked while the solvers are running. */
        void stopButtonClicked();

        /** The apply button was clicked after the solvers are done. */
        void applyButtonClicked();

        /** The discard button was clicked after the solvers are done. */
        void discardButtonClicked();
    }

    /** One solver row: goal name label, progress bar, status text and info button. */
    private static final class Row {
        final ProgressBar bar = new ProgressBar(0);
        final Label status = new Label("");
        final Button info = new Button("Info");
    }

    private final List<Row> rows = new ArrayList<>();
    private final Label overallText = new Label("");
    private final ProgressBar overallBar = new ProgressBar(0);
    private final Button stopButton = new Button("Stop");
    private final Button applyButton = new Button("Apply");
    private final Listener listener;

    private Modus modus = Modus.SOLVERS_RUNNING;
    private Stage stage;

    /**
     * Creates the dialog UI. Must be called on the JavaFX thread; {@link #show()} makes it
     * visible.
     *
     * @param owner the owner window, may be {@code null}
     * @param titles the goal names of the solvers, one row per entry (Swing
     *        {@code prepareDialog} captions)
     * @param listener the button listener
     */
    IsabelleSolverProgressDialogF(@Nullable Window owner, List<String> titles,
            Listener listener) {
        this.listener = listener;
        this.applyButton.setTooltip(new Tooltip(
            "Apply the results (i.e. close goals if the Isabelle solver was successful)"));
        // Swing IsabelleProgressDialog.getApplyButton: apply is disabled while the solvers run
        this.applyButton.setDisable(true);
        this.applyButton.setOnAction(e -> listener.applyButtonClicked());
        this.stopButton.setOnAction(e -> {
            // Swing IsabelleProgressDialog.getStopButton: the same button discards when done
            if (modus == Modus.SOLVERS_DONE) {
                listener.discardButtonClicked();
            }
            if (modus == Modus.SOLVERS_RUNNING) {
                listener.stopButtonClicked();
            }
        });

        GridPane grid = new GridPane();
        grid.setHgap(8);
        grid.setVgap(6);
        grid.setPadding(new Insets(5, 5, 5, 5));
        ColumnConstraints nameColumn = new ColumnConstraints();
        ColumnConstraints progressColumn = new ColumnConstraints();
        progressColumn.setHgrow(Priority.ALWAYS);
        progressColumn.setFillWidth(true);
        grid.getColumnConstraints().addAll(nameColumn, progressColumn);
        // Swing IsabelleProgressDialog titles varargs: the header of the name column is empty and
        // the progress column is titled "Isabelle".
        grid.add(new Label(""), 0, 0);
        grid.add(new Label("Isabelle"), 1, 0);
        for (int i = 0; i < titles.size(); i++) {
            Row row = new Row();
            row.bar.setMaxWidth(Double.MAX_VALUE);
            row.info.setOnAction(e -> listener.infoButtonClicked(rows.indexOf(row)));
            Label title = new Label(titles.get(i));
            HBox progress = new HBox(6, row.bar, row.status, row.info);
            progress.setAlignment(Pos.CENTER_LEFT);
            HBox.setHgrow(row.bar, Priority.ALWAYS);
            grid.add(title, 0, i + 1);
            grid.add(progress, 1, i + 1);
            rows.add(row);
        }

        ScrollPane scroll = new ScrollPane(grid);
        scroll.setFitToWidth(true);
        scroll.setPrefViewportHeight(Math.min(rows.size() * 36 + 40, 300));

        HBox buttonBar = new HBox(5, stopButton, applyButton);
        buttonBar.setAlignment(Pos.CENTER_RIGHT);
        Region spacer = new Region();
        HBox.setHgrow(spacer, Priority.ALWAYS);
        HBox bottom = new HBox(5, spacer, buttonBar);
        bottom.setPadding(new Insets(5, 5, 5, 5));

        HBox top = new HBox(8, overallBar, overallText);
        top.setAlignment(Pos.CENTER_LEFT);
        top.setPadding(new Insets(5, 5, 0, 5));
        overallBar.setMaxWidth(Double.MAX_VALUE);
        HBox.setHgrow(overallBar, Priority.ALWAYS);

        BorderPane root = new BorderPane();
        root.setTop(top);
        root.setCenter(scroll);
        root.setBottom(bottom);

        stage = new Stage();
        if (owner != null) {
            stage.initOwner(owner);
        }
        stage.initModality(Modality.APPLICATION_MODAL);
        stage.setTitle("Isabelle Interface");
        stage.setScene(new Scene(root, 640, 420));
    }

    /** Shows the dialog (non-blocking, Swing shows via {@code SwingUtilities.invokeLater}). */
    void show() {
        stage.show();
    }

    /** Closes the dialog (Swing {@code dispose}). */
    void close() {
        if (stage != null) {
            stage.close();
            stage = null;
        }
    }

    /** Whether the dialog is currently visible (verify harness seam). */
    boolean isShowing() {
        return stage != null && stage.isShowing();
    }

    /** The text of the stop/discard button (verify harness seam). */
    String stopButtonText() {
        return stopButton.getText();
    }

    /** Whether the apply button is enabled (verify harness seam). */
    boolean isApplyEnabled() {
        return !applyButton.isDisabled();
    }

    /** The current modus (verify harness seam). */
    Modus modus() {
        return modus;
    }

    /**
     * Updates the overall progress bar.
     *
     * @param value the number of processed problems (the bar maximum is the problem count)
     */
    void setProgress(int value) {
        double max = Math.max(1, rows.size());
        overallBar.setProgress(Math.min(1.0, value / max));
    }

    /**
     * Sets the overall progress text (Swing {@code setProgressText}: "Preparing..." while the
     * launcher prepares, "Processed X of N problems." afterwards).
     */
    void setOverallText(String text) {
        overallText.setText(text);
    }

    /**
     * Updates the per-solver progress bar.
     *
     * @param row the solver row
     * @param value the progress in {@link #RESOLUTION} units
     */
    void setRowProgress(int row, int value) {
        rows.get(row).bar.setProgress(value / (double) RESOLUTION);
    }

    /**
     * Updates the per-solver status text and colour (a {@code null} colour keeps the default).
     *
     * @param row the solver row
     * @param text the status text
     * @param color the text colour, may be {@code null}
     */
    void setRowText(int row, String text, @Nullable Color color) {
        Label label = rows.get(row).status;
        label.setText(text);
        if (color != null) {
            label.setTextFill(color);
        }
    }

    /**
     * Enables/disables all Info buttons (Swing {@code IsabelleProgressModel.setEditable}: the
     * info buttons become active once the launcher has stopped).
     */
    void setInfoEnabled(boolean enabled) {
        for (Row row : rows) {
            row.info.setDisable(!enabled);
        }
    }

    /**
     * Switches the modus of the dialog and switches/enables the corresponding buttons (Swing
     * {@code IsabelleProgressDialog.setModus}): RUNNING -> the stop button interrupts (apply
     * unavailable), DONE -> the stop button discards (apply available).
     */
    void setModus(Modus m) {
        modus = m;
        switch (modus) {
            case SOLVERS_DONE -> {
                stopButton.setText("Discard");
                applyButton.setDisable(false);
            }
            case SOLVERS_RUNNING -> {
                stopButton.setText("Stop");
                applyButton.setDisable(true);
            }
        }
    }

    /** The number of solver rows (verify harness seam). */
    int rowCount() {
        return rows.size();
    }

    /** The status text of a solver row (verify harness seam). */
    String rowText(int row) {
        return rows.get(row).status.getText();
    }
}

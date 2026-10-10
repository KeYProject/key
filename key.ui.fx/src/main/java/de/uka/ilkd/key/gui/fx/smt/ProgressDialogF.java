/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.smt;

import java.util.List;
import javafx.beans.binding.Bindings;
import javafx.beans.property.BooleanProperty;
import javafx.beans.property.IntegerProperty;
import javafx.beans.property.ObjectProperty;
import javafx.beans.property.SimpleBooleanProperty;
import javafx.beans.property.SimpleIntegerProperty;
import javafx.beans.property.SimpleObjectProperty;
import javafx.beans.property.SimpleStringProperty;
import javafx.beans.property.StringProperty;
import javafx.beans.value.ChangeListener;
import javafx.collections.ObservableList;
import javafx.geometry.Insets;
import javafx.geometry.Pos;
import javafx.scene.Scene;
import javafx.scene.control.Button;
import javafx.scene.control.Label;
import javafx.scene.control.ProgressBar;
import javafx.scene.control.TableCell;
import javafx.scene.control.TableColumn;
import javafx.scene.control.TableView;
import javafx.scene.control.Tooltip;
import javafx.scene.layout.BorderPane;
import javafx.scene.layout.HBox;
import javafx.scene.layout.Priority;
import javafx.scene.layout.StackPane;
import javafx.scene.paint.Color;
import javafx.stage.Modality;
import javafx.stage.Stage;
import javafx.stage.Window;

import de.uka.ilkd.key.gui.fx.IssueDialogF;
import de.uka.ilkd.key.gui.fx.theme.ThemeManager;

/**
 * Dialog showing launched SMT processes and results, counter-part of the Swing
 * {@code de.uka.ilkd.key.gui.smt.ProgressDialog} (key.ui {@code gui/smt/ProgressDialog.java}):
 * an overall progress bar, a table with one row per problem and one process column per solver
 * type (each cell a progress bar with a painted text and an "Info" button opening the
 * {@link InformationWindowF}), and the Stop/Discard, Focus and Apply buttons. The dialog is
 * application modal like the Swing original ({@code setModal(true)}); while the solvers run
 * ({@link Modus#SOLVERS_RUNNING}) only Stop is active, once they are done
 * ({@link Modus#SOLVERS_DONE}) the button becomes Discard and the results may be applied.
 */
public final class ProgressDialogF extends Stage {

    /**
     * Current state of the dialog (Swing {@code ProgressDialog.Modus}).
     */
    public enum Modus {
        /** SMT solvers are running and may be stopped by the user. */
        SOLVERS_RUNNING,
        /** SMT solvers are done (or terminated). Results may be applied by the user. */
        SOLVERS_DONE
    }

    /**
     * Button callbacks, counter-part of the Swing {@code ProgressDialogListener} (the info
     * callback carries the solver index as {@code column} and the problem index as {@code row}).
     */
    public interface Listener {
        void applyButtonClicked();

        void stopButtonClicked();

        void discardButtonClicked();

        void focusButtonClicked();

        void infoButtonClicked(int column, int row);
    }

    /**
     * The state of one (problem, solver) table cell, counter-part of the Swing
     * {@code ProgressModel.ProcessColumn.ProcessData}: an integer progress in
     * {@code [0, resolution]}, the painted text and the text color (the result coloring from
     * {@code SolverListener}: green/red/orange/blue).
     */
    public static final class ProgressCellF {
        final IntegerProperty progress = new SimpleIntegerProperty(0);
        final StringProperty text = new SimpleStringProperty("");
        final ObjectProperty<Color> textColor = new SimpleObjectProperty<>(null);
        final BooleanProperty editable = new SimpleBooleanProperty(false);

        public IntegerProperty progressProperty() {
            return progress;
        }

        public StringProperty textProperty() {
            return text;
        }

        public ObjectProperty<Color> textColorProperty() {
            return textColor;
        }

        public BooleanProperty editableProperty() {
            return editable;
        }
    }

    /**
     * One table row: the problem name and one {@link ProgressCellF} per solver column.
     */
    public static final class ProgressRowF {
        private final String name;
        private final List<ProgressCellF> cells;

        ProgressRowF(String name, List<ProgressCellF> cells) {
            this.name = name;
            this.cells = cells;
        }

        public String getName() {
            return name;
        }

        public List<ProgressCellF> getCells() {
            return cells;
        }
    }

    private final ObservableList<ProgressRowF> rows;
    private final Listener listener;
    private final int resolution;
    private final int max;

    private Modus modus = Modus.SOLVERS_RUNNING;
    private ProgressBar overallBar;
    private Label overallText;
    private Button stopButton;
    private Button focusButton;
    private Button applyButton;

    public ProgressDialogF(Window owner, boolean counterexample, int resolution, int max,
            List<String> titles, ObservableList<ProgressRowF> rows, Listener listener) {
        this.rows = rows;
        this.listener = listener;
        this.resolution = resolution;
        this.max = max;
        setTitle(counterexample ? "SMT Counterexample Search" : "SMT Interface");
        if (owner != null) {
            initOwner(owner);
        }
        initModality(Modality.APPLICATION_MODAL);

        TableView<ProgressRowF> table = new TableView<>(rows);
        table.setEditable(false);
        table.setColumnResizePolicy(TableView.UNCONSTRAINED_RESIZE_POLICY);
        // Swing titles[0] is the empty header of the problem-name column
        TableColumn<ProgressRowF, String> nameCol = new TableColumn<>("");
        nameCol.setCellValueFactory(data -> new SimpleStringProperty(data.getValue().getName()));
        nameCol.setPrefWidth(180);
        table.getColumns().add(nameCol);
        for (int i = 1; i < titles.size(); i++) {
            final int solverIndex = i - 1;
            TableColumn<ProgressRowF, ProgressCellF> col = new TableColumn<>(titles.get(i));
            col.setCellValueFactory(
                data -> new SimpleObjectProperty<>(data.getValue().getCells().get(solverIndex)));
            col.setCellFactory(c -> new ProgressTableCell(solverIndex));
            col.setPrefWidth(230);
            table.getColumns().add(col);
        }

        overallBar = new ProgressBar(0);
        overallText = new Label("");
        StackPane.setAlignment(overallText, Pos.CENTER);
        StackPane overall = new StackPane(overallBar, overallText);
        overallBar.setMaxWidth(Double.MAX_VALUE);
        HBox.setHgrow(overall, Priority.ALWAYS);

        stopButton = new Button("Stop");
        stopButton.setOnAction(e -> {
            if (modus == Modus.SOLVERS_DONE) {
                listener.discardButtonClicked();
            }
            if (modus == Modus.SOLVERS_RUNNING) {
                listener.stopButtonClicked();
            }
        });
        BorderPane pane = new BorderPane();
        pane.setTop(overall);
        HBox buttons = new HBox(5, stopButton);
        if (!counterexample) {
            // like Swing, Focus and Apply are hidden in counterexample mode
            focusButton = new Button("Focus goals");
            focusButton.setTooltip(new Tooltip(
                "Focus open goals to the formulas required to close them"
                    + " (as specified by the SMT solver's unsat core)"));
            focusButton.setDisable(true);
            focusButton.setOnAction(e -> notifySafely(listener::focusButtonClicked));
            applyButton = new Button("Apply");
            applyButton.setTooltip(new Tooltip(
                "Apply the results (i.e. close goals if the SMT solver was successful)"));
            applyButton.setDisable(true);
            applyButton.setOnAction(e -> notifySafely(listener::applyButtonClicked));
            buttons.getChildren().addAll(focusButton, applyButton);
        }
        buttons.setPadding(new Insets(5));
        buttons.setAlignment(Pos.CENTER_RIGHT);
        pane.setBottom(buttons);
        pane.setCenter(table);
        pane.setPadding(new Insets(5));

        Scene scene = new Scene(pane, 780, 420);
        setScene(scene);
        ThemeManager.getInstance().manage(scene);
    }

    private void notifySafely(Runnable call) {
        // like Swing, exceptions during rule application must not be lost (IssueDialog)
        try {
            call.run();
        } catch (RuntimeException exception) {
            IssueDialogF.showExceptionDialog(this, exception);
        }
    }

    /**
     * Sets the overall progress (the number of finished (problem, solver) pairs) and the painted
     * text (Swing {@code SolverListener.setProgressText}).
     *
     * @param finished the number of finished solver runs
     */
    public void setOverallProgress(int finished) {
        overallBar.setProgress(max == 0 ? 0 : (double) finished / max);
        if (max == 1) {
            overallText.setText(finished == 0 ? "Processing..." : "Finished.");
        } else {
            overallText.setText("Processed " + finished + " of " + max + " problems.");
        }
    }

    /**
     * Switches the dialog state (Swing {@code ProgressDialog.setModus}): Stop becomes Discard
     * and the Focus/Apply buttons are enabled once the solvers are done.
     *
     * @param m the new state
     */
    public void setModus(Modus m) {
        modus = m;
        switch (modus) {
            case SOLVERS_DONE -> {
                stopButton.setText("Discard");
                if (applyButton != null) {
                    applyButton.setDisable(false);
                }
                if (focusButton != null) {
                    focusButton.setDisable(false);
                }
            }
            case SOLVERS_RUNNING -> {
                stopButton.setText("Stop");
                if (applyButton != null) {
                    applyButton.setDisable(true);
                }
            }
        }
    }

    /**
     * Marks every cell editable (Swing {@code ProgressModel.setEditable}, called when all
     * solvers are finished): the "Info" buttons of the cells become clickable.
     */
    public void setEditable() {
        for (ProgressRowF row : rows) {
            for (ProgressCellF cell : row.getCells()) {
                cell.editable.set(true);
            }
        }
    }

    /**
     * The cell of one process column: a progress bar with the painted text on top and an
     * "Info" button, counter-part of the Swing {@code ProgressTable.ProgressPanel}. The cell
     * re-binds its controls whenever the table hands it another {@link ProgressCellF}.
     */
    private final class ProgressTableCell extends TableCell<ProgressRowF, ProgressCellF> {

        private final ProgressBar bar = new ProgressBar(0);
        private final Label text = new Label();
        private final Button info = new Button("Info");
        private final StackPane stack = new StackPane(bar, text);
        private final HBox box = new HBox(4, stack, info);
        private final int solverIndex;

        private ProgressCellF bound;
        private ChangeListener<Color> colorListener;

        ProgressTableCell(int solverIndex) {
            this.solverIndex = solverIndex;
            bar.setMaxWidth(Double.MAX_VALUE);
            HBox.setHgrow(stack, Priority.ALWAYS);
            StackPane.setAlignment(text, Pos.CENTER);
            info.setPrefWidth(56);
            box.setPadding(new Insets(2));
            itemProperty().addListener((obs, old, value) -> rebind(old, value));
        }

        private void rebind(ProgressCellF old, ProgressCellF cell) {
            if (bound != null) {
                bar.progressProperty().unbind();
                text.textProperty().unbind();
                info.disableProperty().unbind();
                if (colorListener != null) {
                    bound.textColorProperty().removeListener(colorListener);
                }
                text.setTextFill(null);
                bar.setStyle("");
                bound = null;
            }
            if (cell != null) {
                bound = cell;
                bar.progressProperty().bind(
                    Bindings.divide(cell.progressProperty(), (double) resolution));
                text.textProperty().bind(cell.textProperty());
                info.disableProperty().bind(cell.editableProperty().not());
                colorListener = (obs, o, n) -> applyColors(cell);
                cell.textColorProperty().addListener(colorListener);
                applyColors(cell);
            }
        }

        private void applyColors(ProgressCellF cell) {
            Color color = cell.textColor.get();
            text.setTextFill(color);
            bar.setStyle(color == null ? "" : "-fx-accent: " + toHex(color) + ";");
        }

        @Override
        protected void updateItem(ProgressCellF item, boolean empty) {
            super.updateItem(item, empty);
            if (empty || item == null) {
                setGraphic(null);
                info.setOnAction(null);
            } else {
                setGraphic(box);
                info.setOnAction(e -> listener.infoButtonClicked(solverIndex, getIndex()));
            }
        }

        private String toHex(Color color) {
            return String.format("#%02x%02x%02x", (int) Math.round(color.getRed() * 255),
                (int) Math.round(color.getGreen() * 255),
                (int) Math.round(color.getBlue() * 255));
        }
    }
}

/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.tacletmatch.classic;

import javafx.beans.property.SimpleStringProperty;
import javafx.collections.FXCollections;
import javafx.geometry.Insets;
import javafx.scene.Node;
import javafx.scene.Scene;
import javafx.scene.control.Label;
import javafx.scene.control.Tab;
import javafx.scene.control.TabPane;
import javafx.scene.control.TableColumn;
import javafx.scene.control.TableView;
import javafx.scene.control.TextArea;
import javafx.scene.control.TextField;
import javafx.scene.control.cell.TextFieldTableCell;
import javafx.scene.layout.Priority;
import javafx.scene.layout.Region;
import javafx.scene.layout.VBox;
import javafx.stage.Window;

import de.uka.ilkd.key.control.ProofControl;
import de.uka.ilkd.key.control.instantiation_model.TacletFindModel;
import de.uka.ilkd.key.control.instantiation_model.TacletInstantiationModel;
import de.uka.ilkd.key.gui.fx.tacletmatch.ApplyTacletDialogF;
import de.uka.ilkd.key.gui.fx.tacletmatch.ExpandableTextF;
import de.uka.ilkd.key.gui.fx.tacletmatch.MatchInfoPanelF;
import de.uka.ilkd.key.gui.fx.tacletmatch.TmPrintF;
import de.uka.ilkd.key.gui.fx.theme.ThemeManager;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.SVInstantiationExceptionWithPosition;
import de.uka.ilkd.key.rule.Taclet;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * The classic (table-based) dialog for completing and applying an interactively selected taclet —
 * the JavaFX migration fallback of the redesigned {@code TacletMatchDialogF}.
 *
 * <p>
 * Port of {@code de.uka.ilkd.key.gui.tacletmatch.classic.TacletMatchCompletionDialog} plus the
 * chrome helpers of its base {@code de.uka.ilkd.key.gui.tacletmatch.classic.ApplyTacletDialog}
 * (both module {@code key.ui}), which the shared FX base {@link ApplyTacletDialogF} does not
 * carry: the taclet display, the sequent program-variables info, the validation status area and
 * the button panel. Per instantiation alternative it shows a table of the schema-variable
 * instantiations (Swing {@code DataTable}; editing commits write straight into the {@link
 * TacletFindModel} and refresh the status, like the Swing {@code editingStopped}), and — for
 * taclets with an {@code \assumes} sequent — a {@link TacletIfSelectionDialogF}.
 *
 * <p>
 * Deviations, all visual or Swing-table artifacts: the multiline editor with the +/- row-height
 * buttons becomes a plain single-line text cell (long instantiations are better edited in the
 * redesigned dialog's larger editor); the drag-and-drop of sub-terms onto the table (Swing
 * {@code DropTarget}) is deferred with the sequent view's drag source; window preferences are not
 * persisted (the FX UI has no per-dialog preference store yet). The error-position focus routing
 * ({@code errorPositionKnown}) ports as far as a JavaFX table cell editor allows — the row is
 * selected and scrolled to, and the caret position is set on the text field — with the same
 * caveat the Swing original documents itself ("ALL THIS DOES NOT REALLY WORK!!!").
 */
public class TacletMatchCompletionDialogF extends ApplyTacletDialogF {

    private static final Logger LOGGER =
        LoggerFactory.getLogger(TacletMatchCompletionDialogF.class);

    private final Services services;
    private final NotationInfo notationInfo;

    /** the current chosen model */
    private int current = 0;

    /** the gui component used to display the different instantiation alternatives */
    private TabPane alternatives;

    /** the validation status area (Swing {@code createStatusPanel}) */
    private TextArea statusArea;

    /** the data tables, one per alternative (Swing {@code DataTable}) */
    private final TableView<Row>[] dataTables;

    /** the if-selections, one per alternative or {@code null} (Swing {@code ifSelectionPanel}) */
    private final TacletIfSelectionDialogF[] ifSelections;

    @SuppressWarnings("unchecked")
    public TacletMatchCompletionDialogF(Window owner, TacletInstantiationModel[] model, Goal goal,
            Services services, NotationInfo notationInfo, ProofControl proofControl) {
        super(owner, "Choose Taclet Instantiation", model, proofControl, goal);
        this.services = services;
        this.notationInfo = notationInfo;
        this.current = 0;
        this.dataTables = new TableView[model.length];
        this.ifSelections = new TacletIfSelectionDialogF[model.length];

        for (TacletInstantiationModel aModel : model) {
            aModel.prepareUnmatchedInstantiation();
        }

        VBox root = new VBox(4);
        root.setPadding(new Insets(8));
        root.getChildren().add(createTacletDisplay());

        VBox lower = new VBox(4);
        Node instArea = createInstantiationArea();
        lower.getChildren().add(instArea);
        VBox.setVgrow(instArea, Priority.ALWAYS);
        lower.getChildren().add(createInfoPanel());
        lower.getChildren().add(createStatusPanel());
        root.getChildren().add(lower);
        VBox.setVgrow(lower, Priority.ALWAYS);

        Scene scene = new Scene(root, 760, 640);
        ThemeManager.getInstance().style(scene);
        setScene(scene);
        setMinWidth(620);
        setMinHeight(480);
        setStatus(model[current()].getStatusString());
        if (owner != null) {
            centerOn(owner);
        }
        show();
        LOGGER.info("TacletMatchCompletionDialogF opened: alternatives={} taclet={}", model.length,
            model[0].taclet().name());
    }

    private void centerOn(Window owner) {
        double x = owner.getX() + (owner.getWidth() - getWidth()) / 2;
        double y = owner.getY() + (owner.getHeight() - getHeight()) / 2;
        setX(Math.max(0, x));
        setY(Math.max(0, y));
    }

    /**
     * the taclet display (Swing {@code classic.ApplyTacletDialog.createTacletDisplay}): the
     * selected taclet printed as read-only text. Like the redesigned dialog, the printing hides
     * term labels ({@link TmPrintF}); the Swing classic shows the mediator's visible term labels —
     * the FX UI has no term-label visibility menu yet (M2c leftover), so the shared no-labels
     * printing is used.
     */
    private javafx.scene.Node createTacletDisplay() {
        VBox panel = new VBox(2);
        panel.getChildren()
                .add(MatchInfoPanelF.sectionTitle(
                    "Selected Taclet - " + model[0].taclet().name()));

        Taclet taclet = model[0].taclet();
        LOGGER.debug("TacletApp: {}", taclet);

        TextArea text = new TextArea(
            TmPrintF.taclet(services, notationInfo, taclet));
        text.setEditable(false);
        text.setWrapText(false);
        text.setFont(ExpandableTextF.mono());
        // Swing shows at most 11 lines; the rest scrolls
        text.setPrefRowCount(11);
        panel.getChildren().add(text);
        return panel;
    }

    /**
     * the tabbed instantiation alternatives (Swing {@code createTacletPanel}): one table per
     * alternative plus the if-selection where the taclet has an {@code \assumes} sequent.
     */
    private javafx.scene.Node createInstantiationArea() {
        VBox panel = new VBox(2);
        panel.getChildren().add(MatchInfoPanelF.sectionTitle("Variable Instantiations"));

        alternatives = new TabPane();
        for (int i = 0; i < model.length; i++) {
            VBox tabContent = new VBox(4);
            tabContent.setPadding(new Insets(4));
            TableView<Row> table = createInstantiationDisplay(i);
            tabContent.getChildren().add(table);
            if (!model[i].application().taclet().assumesSequent().isEmpty()) {
                TacletIfSelectionDialogF ifSelection =
                    new TacletIfSelectionDialogF(model[i], services, notationInfo);
                ifSelections[i] = ifSelection;
                tabContent.getChildren().add(ifSelection);
            }
            Tab t = new Tab("Alt " + i, tabContent);
            t.setClosable(false);
            alternatives.getTabs().add(t);
        }
        alternatives.getSelectionModel().selectedIndexProperty().addListener((obs, o, n) -> {
            current = n.intValue();
            setStatus(model[current()].getStatusString());
        });
        VBox.setVgrow(alternatives, Priority.ALWAYS);
        panel.getChildren().add(alternatives);
        return panel;
    }

    /**
     * the instantiation table of one alternative (Swing {@code DataTable}): the model rows with
     * the schema variable name and its instantiation; the rows after the match-determined ones are
     * editable, and each committed edit is written into the {@link TacletFindModel} and refreshes
     * the status (Swing {@code editingStopped} + {@code checkAfterEachInput}).
     */
    private TableView<Row> createInstantiationDisplay(int i) {
        TacletFindModel tm = model[i].tableModel();
        var items = FXCollections.<Row>observableArrayList();
        for (int r = 0; r < tm.getRowCount(); r++) {
            Object name = tm.getValueAt(r, 0);
            Object value = tm.getValueAt(r, 1);
            items.add(new Row(String.valueOf(name), value == null ? "" : String.valueOf(value),
                tm.isCellEditable(r, 1), r));
        }

        TableView<Row> table = new TableView<>(items);
        table.setEditable(true);
        table.setColumnResizePolicy(TableView.CONSTRAINED_RESIZE_POLICY_FLEX_LAST_COLUMN);
        table.setPlaceholder(new Label("No schema variables"));

        TableColumn<Row, String> varCol = new TableColumn<>("Variable");
        varCol.setCellValueFactory(c -> new javafx.beans.property.SimpleStringProperty(
            c.getValue().getVarName()));
        varCol.setPrefWidth(160);

        TableColumn<Row, String> instCol = new TableColumn<>("Instantiation");
        instCol.setCellValueFactory(c -> c.getValue().valueProperty());
        instCol.setCellFactory(col -> new TextFieldTableCell<Row, String>() {
            {
                setConverter(new javafx.util.StringConverter<>() {
                    @Override
                    public String toString(String object) {
                        return object == null ? "" : object;
                    }

                    @Override
                    public String fromString(String string) {
                        return string;
                    }
                });
            }

            @Override
            public void startEdit() {
                // refuse editing the match-determined rows (Swing: isCellEditable)
                if (getTableRow() != null && getTableRow().getItem() instanceof Row row
                        && row.isEditable()) {
                    super.startEdit();
                }
            }

            @Override
            public void updateItem(String item, boolean empty) {
                super.updateItem(item, empty);
                if (empty || item == null) {
                    setText(null);
                    getStyleClass().remove("tacletmatch-muted");
                    return;
                }
                setText(item);
                boolean editableRow = getTableRow() != null
                        && getTableRow().getItem() instanceof Row row && row.isEditable();
                if (!editableRow && !getStyleClass().contains("tacletmatch-muted")) {
                    getStyleClass().add("tacletmatch-muted");
                } else if (editableRow) {
                    getStyleClass().remove("tacletmatch-muted");
                }
            }
        });
        instCol.setOnEditCommit(e -> {
            Row row = e.getRowValue();
            row.setValue(e.getNewValue());
            model[i].tableModel().setValueAt(e.getNewValue(), row.getModelRow(), 1);
            // Swing editingStopped: push the input and re-validate after each input
            pushAllInputToModel(i);
            setStatus(model[current()].getStatusString());
        });
        table.getColumns().setAll(varCol, instCol);

        // Swing adapts the table height to min(rowCount, 8) rows of 48px; here the table grows
        // with its content and is bounded by the surrounding scroll/ VBox layout
        table.setPrefHeight(Math.min(items.size(), 8) * 28 + 30);
        table.setMinHeight(Region.USE_PREF_SIZE);

        dataTables[i] = table;
        return table;
    }

    /**
     * the sequent program variables info (Swing {@code classic.ApplyTacletDialog.createInfoPanel})
     */
    private javafx.scene.Node createInfoPanel() {
        VBox panel = new VBox(2);
        panel.getChildren().add(MatchInfoPanelF.sectionTitle("Sequent program variables"));
        var vars = model[0].programVariables();
        StringBuilder sb = new StringBuilder();
        boolean first = true;
        for (IProgramVariable v : vars.elements()) {
            if (!first) {
                sb.append(", ");
            }
            first = false;
            sb.append(v);
        }
        TextArea text = new TextArea(sb.length() == 0 ? "none" : sb.toString());
        text.setEditable(false);
        text.setPrefRowCount(2);
        text.setWrapText(true);
        panel.getChildren().add(text);
        return panel;
    }

    /** the validation status area (Swing {@code classic.ApplyTacletDialog.createStatusPanel}) */
    private javafx.scene.Node createStatusPanel() {
        VBox panel = new VBox(2);
        panel.getChildren().add(MatchInfoPanelF.sectionTitle("Input validation result"));
        statusArea = new TextArea();
        statusArea.setEditable(false);
        statusArea.setWrapText(true);
        statusArea.setPrefRowCount(2);
        panel.getChildren().add(statusArea);
        setStatus(model[current()].getStatusString());
        return panel;
    }

    /**
     * the current selected model (Swing {@code current()}): the selected tab's index.
     */
    @Override
    protected int current() {
        return alternatives == null ? 0 : alternatives.getSelectionModel().getSelectedIndex();
    }

    @Override
    protected void pushAllInputToModel() {
        pushAllInputToModel(current());
    }

    /** pushes the if-selection and the table edits of alternative {@code i} into its model */
    private void pushAllInputToModel(int i) {
        if (ifSelections[i] != null) {
            ifSelections[i].pushAllInputToModel();
        }
        // table edits are committed cell-by-cell; nothing further to push here
    }

    @Override
    protected void setStatus(String s) {
        if (statusArea != null) {
            statusArea.setText(s == null ? "" : s);
        }
    }

    @Override
    protected void onApplyException(Exception exc) {
        // Swing errorPositionKnown: select the input where the error occurred and place the caret
        if (exc instanceof SVInstantiationExceptionWithPosition ex) {
            focusErrorPosition(ex);
        }
        super.onApplyException(exc);
    }

    /**
     * Swing {@code ButtonListener.errorPositionKnown}: the offending instantiation input is
     * selected and the caret placed at the reported column. As the Swing original documents, the
     * caret part is best-effort; the FX table cell editor is only alive while it has focus, so
     * only row selection and scroll-into-view are guaranteed.
     */
    private void focusErrorPosition(SVInstantiationExceptionWithPosition ex) {
        TableView<Row> table = dataTables[current()];
        int row = ex.getPosition().line() - 1;
        if (ex.inIfSequent()) {
            ifSelections[current()].requestFocusAt(row, ex.getPosition().column());
            return;
        }
        var items = table.getItems();
        if (row >= 0 && row < items.size()) {
            table.getSelectionModel().select(row);
            table.scrollTo(row);
            table.layout();
            TextField editor = (TextField) table.lookup(".text-field");
            if (editor != null) {
                try {
                    editor.positionCaret(Math.max(0, ex.getPosition().column() - 1));
                } catch (RuntimeException e) {
                    LOGGER.debug("tacletmatchcompletiondialogf: caret position calculation "
                        + "failed", e);
                }
                editor.requestFocus();
            }
        }
    }

    /** cancels the dialog (used by the self-test hook; identical to the Cancel button) */
    public void cancelAndClose() {
        closeDialog();
    }

    /**
     * the number of instantiation rows of the current alternative (used by the self-test hook to
     * assert the table renders)
     */
    public int tableRowCount() {
        return current < dataTables.length && dataTables[current] != null
                ? dataTables[current].getItems().size()
                : 0;
    }

    /** one row of the instantiation table (Swing {@code DataTable} row) */
    private static final class Row {
        private final String varName;
        private final SimpleStringProperty value;
        private final boolean editable;
        private final int modelRow;

        Row(String varName, String value, boolean editable, int modelRow) {
            this.varName = varName;
            this.value = new SimpleStringProperty(value);
            this.editable = editable;
            this.modelRow = modelRow;
        }

        String getVarName() {
            return varName;
        }

        SimpleStringProperty valueProperty() {
            return value;
        }

        String getValue() {
            return value.get();
        }

        void setValue(String v) {
            value.set(v);
        }

        boolean isEditable() {
            return editable;
        }

        int getModelRow() {
            return modelRow;
        }
    }
}

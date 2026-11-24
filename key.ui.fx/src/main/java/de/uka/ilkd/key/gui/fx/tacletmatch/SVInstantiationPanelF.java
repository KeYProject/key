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
import javafx.scene.Scene;
import javafx.scene.control.Button;
import javafx.scene.control.Label;
import javafx.scene.control.TextArea;
import javafx.scene.control.Tooltip;
import javafx.scene.input.DataFormat;
import javafx.scene.input.DragEvent;
import javafx.scene.input.TransferMode;
import javafx.scene.layout.GridPane;
import javafx.scene.layout.HBox;
import javafx.scene.layout.Priority;
import javafx.scene.layout.VBox;
import javafx.stage.Modality;
import javafx.stage.Stage;
import javafx.stage.Window;
import javafx.util.Duration;

import de.uka.ilkd.key.control.instantiation_model.TacletFindModel;
import de.uka.ilkd.key.control.instantiation_model.TacletInstantiationModel;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.pp.NotationInfo;

import org.key_project.logic.op.sv.SchemaVariable;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Panel for the schema variables the user still has to instantiate: those occurring only in
 * {@code \add}/{@code \replacewith}/{@code \assumes}, not determined by the find match (the
 * find-determined ones are shown read-only in {@link MatchInfoPanelF}). Each row offers the
 * proposal pre-filled by the model, accepts drag-and-drop of a text from the sequent, and writes
 * its input back to the shared {@link TacletFindModel}, refreshing the dialog status on change.
 *
 * <p>
 * Port of {@code de.uka.ilkd.key.gui.tacletmatch.SVInstantiationPanel} (SVInstantiationPanel.java:
 * 56-449). Event semantics preserved: every text change schedules a debounced
 * {@link #pushAndRefresh()} (the Swing 300&nbsp;ms single-shot {@code Timer} becomes a
 * {@link PauseTransition}), a focus loss pushes immediately, an expand toggle grows the field,
 * an edit button opens a larger editor, and dropping text inserts it at the caret. The Swing
 * version additionally accepted the sequent's {@code PosInSequentTransferable} flavour
 * (SVInstantiationPanel.java:219-247); the FX sequent view has no drag source yet (sequent-audit
 * P7), so only plain-text drops are handled for now.
 */
class SVInstantiationPanelF extends VBox {

    private static final Logger LOGGER = LoggerFactory.getLogger(SVInstantiationPanelF.class);

    /** above this many editable variables, lay the fields out in two columns */
    private static final int TWO_COLUMN_THRESHOLD = 3;

    /** debounce for refreshing the status/preview while typing (SVInstantiationPanel.java:72) */
    private static final Duration REFRESH_DEBOUNCE = Duration.millis(300);

    private final TacletFindModel tableModel;
    private final Services services;
    private final NotationInfo notationInfo;
    private final Runnable onChange;

    /** the editable rows: the model-row index and the field carrying its input */
    private record Row(int modelRow, SvField field) {
    }

    private final List<Row> rows = new ArrayList<>();

    /** debounce for refreshing the status/preview while typing */
    private PauseTransition refreshTimer;

    SVInstantiationPanelF(TacletInstantiationModel model, Services services,
            NotationInfo notationInfo, Runnable onChange) {
        this.tableModel = model.tableModel();
        this.services = services;
        this.notationInfo = notationInfo;
        this.onChange = onChange;

        build();
    }

    private void build() {
        getStyleClass().add("tacletmatch-section-holder");
        List<Node> rowComps = new ArrayList<>();
        int colorIndex = 0;
        for (int r = 0; r < tableModel.getRowCount(); r++) {
            if (!tableModel.isCellEditable(r, 1)) {
                continue;
            }
            SchemaVariable sv = (SchemaVariable) tableModel.getValueAt(r, 0);
            Object value = tableModel.getValueAt(r, 1);

            SvField field = new SvField(value == null ? "" : value.toString());
            field.area.focusedProperty().addListener((obs, was, focused) -> {
                if (!focused) {
                    pushAndRefresh();
                }
            });
            // refresh status and preview after a short typing pause, not only on focus change
            field.area.textProperty().addListener((obs, oldText, newText) -> scheduleRefresh());
            installDropTarget(field);

            rows.add(new Row(r, field));
            rowComps.add(rowComponent(SvPaletteF.chip(sv.name().toString(), colorIndex++),
                field.component));
        }

        VBox content = new VBox(4);
        if (rowComps.isEmpty()) {
            Label none = TmStyleF.muted("All schema variables are determined by the match.");
            content.getChildren().add(none);
        } else if (rowComps.size() > TWO_COLUMN_THRESHOLD) {
            // many variables: two columns to stay compact
            GridPane grid = new GridPane();
            grid.setHgap(16);
            grid.setVgap(4);
            int col = 0;
            int row = 0;
            for (Node rc : rowComps) {
                grid.add(rc, col, row);
                if (++col == 2) {
                    col = 0;
                    row++;
                }
            }
            content.getChildren().add(grid);
        } else {
            content.getChildren().addAll(rowComps);
        }

        getChildren().add(TmStyleF.section("Instantiate schema variables", content));
    }

    private Node rowComponent(Label chip, Node field) {
        HBox west = new HBox(4);
        west.setAlignment(Pos.CENTER_LEFT);
        west.getChildren().addAll(chip, new Label("↦"));

        HBox p = new HBox(6);
        p.getStyleClass().add("tacletmatch-row");
        p.setPadding(new Insets(2, 0, 2, 0));
        p.setAlignment(Pos.CENTER_LEFT);
        p.getChildren().addAll(west, field);
        HBox.setHgrow(field, Priority.ALWAYS);
        return p;
    }

    /** writes every field's text back to the model (SVInstantiationPanel.java:184-188) */
    public void pushAllInputToModel() {
        for (Row row : rows) {
            tableModel.setValueAt(row.field().getText(), row.modelRow(), 1);
        }
    }

    private void pushAndRefresh() {
        pushAllInputToModel();
        if (onChange != null) {
            onChange.run();
        }
    }

    /**
     * debounces {@link #pushAndRefresh()} so typing updates the status/preview after a pause
     * (SVInstantiationPanel.java:197-204).
     */
    private void scheduleRefresh() {
        if (refreshTimer == null) {
            refreshTimer = new PauseTransition(REFRESH_DEBOUNCE);
            refreshTimer.setOnFinished(e -> pushAndRefresh());
        }
        refreshTimer.playFromStart();
    }

    /**
     * accepts plain-text drops and inserts them at the caret (SVInstantiationPanel.java:206-248)
     */
    private void installDropTarget(SvField field) {
        field.area.setOnDragOver((DragEvent event) -> {
            if (event.getDragboard().hasContent(DataFormat.PLAIN_TEXT)) {
                event.acceptTransferModes(TransferMode.MOVE, TransferMode.COPY);
                field.setDropHighlight(true);
                event.consume();
            }
        });
        field.area.setOnDragExited(e -> field.setDropHighlight(false));
        field.area.setOnDragDropped((DragEvent event) -> {
            field.setDropHighlight(false);
            var db = event.getDragboard();
            if (db.hasContent(DataFormat.PLAIN_TEXT)) {
                String s = (String) db.getContent(DataFormat.PLAIN_TEXT);
                field.area.insertText(field.area.getCaretPosition(), s == null ? "" : s);
                field.autoExpandIfMultiline();
                pushAndRefresh();
                event.setDropCompleted(true);
            }
            event.consume();
        });
    }

    /**
     * An editable instantiation field that shows long, possibly multi-line content nicely: a single
     * line by default, expandable to several lines (scrolling beyond) via a small toggle, so a
     * dropped term does not blow up the dialog (SVInstantiationPanel.java:266-419).
     */
    private final class SvField {
        private final TextArea area = new TextArea();
        private final Button toggle;
        private final Button edit;
        private final HBox component;
        private boolean expanded;

        SvField(String value) {
            area.setText(value);
            area.getStyleClass().add(TmStyleF.MONO_CLASS);
            area.setWrapText(true);
            area.setPrefRowCount(1);
            // a hint that the field accepts a dropped sub-term, shown only while empty/unfocused:
            // the FX prompt text already has exactly this behaviour
            area.setPromptText("drop a term or type…");

            toggle = TmStyleF.disclosure("the whole instantiation");
            toggle.setOnAction(e -> setExpanded(!expanded));

            // the inline field stays small; an edit icon opens a larger, resizable editor for
            // comfortably entering long instantiations (SVInstantiationPanel.java:319-326)
            edit = new Button("✎");
            edit.getStyleClass().add("tacletmatch-edit-button");
            edit.setFocusTraversable(false);
            edit.setTooltip(new Tooltip("Edit in a larger, resizable window"));
            edit.setOnAction(e -> openInEditor());

            HBox controls = new HBox(2, toggle, edit);
            controls.setAlignment(Pos.TOP_LEFT);

            component = new HBox(4, area, controls);
            component.setAlignment(Pos.TOP_LEFT);
            HBox.setHgrow(area, Priority.ALWAYS);
            updateHeight();
        }

        String getText() {
            return area.getText();
        }

        void autoExpandIfMultiline() {
            if (!expanded && area.getText().indexOf('\n') >= 0) {
                setExpanded(true);
            }
        }

        private void setExpanded(boolean e) {
            expanded = e;
            TmStyleF.setDisclosure(toggle, e);
            updateHeight();
        }

        void setDropHighlight(boolean on) {
            if (on) {
                if (!area.getStyleClass().contains("tacletmatch-drop-highlight")) {
                    area.getStyleClass().add("tacletmatch-drop-highlight");
                }
            } else {
                area.getStyleClass().remove("tacletmatch-drop-highlight");
            }
        }

        /**
         * opens the field's content in a larger, resizable editor window; on OK the edited text
         * replaces the field's content (which refreshes the status/preview as usual)
         * (SVInstantiationPanel.java:373-408).
         */
        private void openInEditor() {
            Window owner = component.getScene() != null ? component.getScene().getWindow() : null;
            Stage dlg = new Stage();
            if (owner instanceof Stage s) {
                dlg.initOwner(s);
            }
            dlg.initModality(Modality.APPLICATION_MODAL);
            dlg.setTitle("Edit instantiation");

            TextArea ta = new TextArea(area.getText());
            ta.getStyleClass().add(TmStyleF.MONO_CLASS);
            ta.setWrapText(true);
            ta.setPrefRowCount(14);

            Button ok = new Button("OK");
            Button cancel = new Button("Cancel");
            ok.setDefaultButton(true);
            ok.setOnAction(e -> {
                area.setText(ta.getText());
                autoExpandIfMultiline();
                dlg.close();
            });
            cancel.setCancelButton(true);
            cancel.setOnAction(e -> dlg.close());

            HBox buttons = new HBox(8, cancel, ok);
            buttons.setAlignment(Pos.CENTER_RIGHT);
            buttons.setPadding(new Insets(8, 0, 0, 0));

            VBox content = new VBox(8, ta, buttons);
            content.setPadding(new Insets(8));
            dlg.setScene(new Scene(content, 480, 320));
            dlg.show();
            ta.requestFocus();
        }

        private void updateHeight() {
            area.setPrefRowCount(expanded ? 5 : 1);
        }
    }
}

/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.tacletmatch.classic;

import java.util.ArrayList;
import java.util.List;
import javafx.geometry.Insets;
import javafx.scene.control.ComboBox;
import javafx.scene.control.Label;
import javafx.scene.control.ListCell;
import javafx.scene.control.TextField;
import javafx.scene.layout.HBox;
import javafx.scene.layout.Priority;
import javafx.scene.layout.VBox;

import de.uka.ilkd.key.control.instantiation_model.TacletAssumesModel;
import de.uka.ilkd.key.control.instantiation_model.TacletInstantiationModel;
import de.uka.ilkd.key.gui.fx.tacletmatch.ExpandableTextF;
import de.uka.ilkd.key.gui.fx.tacletmatch.MatchInfoPanelF;
import de.uka.ilkd.key.gui.fx.tacletmatch.TmTextF;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.proof.io.ProofSaver;

import org.key_project.prover.rules.instantiation.AssumesFormulaInstantiation;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * This panel appears if a rule is selected to be applied and the rule has an if sequent. The panel
 * offers the possibility to select the wanted match of the if sequent or to enter the if-sequent
 * instantiation manually.
 *
 * <p>
 * Port of {@code de.uka.ilkd.key.gui.tacletmatch.classic.TacletIfSelectionDialog} (module {@code
 * key.ui}): per {@code \assumes} formula one row with the printed formula label, a {@link
 * ComboBox} of the candidate instantiations (backed by the Swing {@code TacletAssumesModel}, whose
 * last element is the "Manual Input" sentinel) and — when manual input is selected — a text field
 * whose content is written to the model on change/focus loss.
 */
class TacletIfSelectionDialogF extends VBox {

    private static final Logger LOGGER = LoggerFactory.getLogger(TacletIfSelectionDialogF.class);

    private final TacletInstantiationModel model;
    private final Services services;
    private final NotationInfo notationInfo;

    /** one row per assumes formula */
    private final List<IfRow> rows = new ArrayList<>();

    private record IfRow(int index, TacletAssumesModel choice,
            ComboBox<AssumesFormulaInstantiation> combo,
            TextField manual) {
    }

    TacletIfSelectionDialogF(TacletInstantiationModel model, Services services,
            NotationInfo notationInfo) {
        this.model = model;
        this.services = services;
        this.notationInfo = notationInfo;

        getStyleClass().add("tacletmatch-section");
        getChildren()
                .add(MatchInfoPanelF.sectionTitle("Please instantiate the taclet's assumptions:"));
        getChildren().add(createIfPanel());
    }

    /**
     * creates the rows used to select the wanted if instantiation. If the if-sequent matches
     * different parts of the sequent the user can choose the right one or enter an instantiation
     * manually (in which case a cut is performed if the manual entry does not match any other part
     * of the sequent).
     */
    private VBox createIfPanel() {
        VBox panel = new VBox(4);
        panel.setPadding(new Insets(4, 0, 4, 0));
        for (int i = 0; i < model.ifChoiceModelCount(); i++) {
            panel.getChildren().add(buildFormulaSelector(i));
        }
        return panel;
    }

    private HBox buildFormulaSelector(int index) {
        TacletAssumesModel choice = model.ifChoiceModel(index);

        Label label = new Label(ProofSaver.printAnything(model.ifFma(index), services));
        label.getStyleClass().add("tacletmatch-muted");
        label.setPrefWidth(140);
        label.setWrapText(true);

        ComboBox<AssumesFormulaInstantiation> combo = new ComboBox<>();
        for (int k = 0; k < choice.getSize(); k++) {
            combo.getItems().add(choice.getElementAt(k));
        }
        // preselect the model's current selection (never the sentinel if a candidate exists)
        Object selected = choice.getSelectedItem();
        int selIdx = -1;
        for (int k = 0; k < combo.getItems().size(); k++) {
            if (combo.getItems().get(k) == selected) {
                selIdx = k;
                break;
            }
        }
        if (selIdx < 0 && !combo.getItems().isEmpty()) {
            selIdx = combo.getItems().size() - 1;
        }
        if (selIdx >= 0) {
            combo.getSelectionModel().select(selIdx);
        }
        combo.setCellFactory(view -> new ListCell<>() {
            @Override
            protected void updateItem(AssumesFormulaInstantiation item, boolean empty) {
                super.updateItem(item, empty);
                if (empty || item == null) {
                    setText(null);
                    setTooltip(null);
                } else {
                    setText(TmTextF.collapseToLine(item.toString(), 160));
                    setTooltip(new javafx.scene.control.Tooltip(item.toString()));
                }
            }
        });
        combo.setButtonCell(new ListCell<>() {
            @Override
            protected void updateItem(AssumesFormulaInstantiation item, boolean empty) {
                super.updateItem(item, empty);
                setText(empty || item == null ? null : item.toString());
            }
        });

        TextField manual = new TextField();
        manual.setPromptText("manual instantiation");
        manual.setFont(ExpandableTextF.mono());
        manual.setManaged(false);
        manual.setVisible(false);
        HBox.setHgrow(manual, Priority.ALWAYS);

        TextField manualRef = manual;
        combo.getSelectionModel().selectedItemProperty().addListener((obs, oldV, newV) -> {
            boolean isManual = newV != null && choice.isManualInputSelected();
            manualRef.setManaged(isManual);
            manualRef.setVisible(isManual);
            pushAllInputToModel();
        });
        manualRef.textProperty().addListener((o, a, b) -> pushAllInputToModel());
        manualRef.focusedProperty().addListener((obs, was, is) -> {
            if (was && !is) {
                pushAllInputToModel();
            }
        });
        manualRef.setOnAction(e -> pushAllInputToModel());

        HBox row = new HBox(6, label, combo, manual);
        HBox.setHgrow(combo, Priority.ALWAYS);
        rows.add(new IfRow(index, choice, combo, manual));
        return row;
    }

    /**
     * the if selection panel is attached to exactly one model (Swing {@code current()}); the
     * manual inputs are transferred to that model.
     */
    public void pushAllInputToModel() {
        for (IfRow row : rows) {
            if (row.combo().getSelectionModel().getSelectedItem() != null
                    && row.choice().isManualInputSelected()
                    && row.manual().getText() != null && !row.manual().getText().isEmpty()) {
                model.setManualInput(row.index(), row.manual().getText());
            } else {
                model.setManualInput(row.index(), "");
            }
        }
    }

    /**
     * requests focus for the {@code field}-th manual input field and places the caret at the given
     * column (Swing {@code requestFocusAt}); best-effort as in the Swing original.
     */
    public void requestFocusAt(int field, int col) {
        if (field < 0 || field >= rows.size()) {
            LOGGER.debug("None existing field requested");
            return;
        }
        TextField tf = rows.get(field).manual();
        if (tf != null && col >= 0) {
            try {
                tf.positionCaret(Math.max(0, col - 1));
            } catch (RuntimeException iae) {
                LOGGER.debug("Something is wrong with the caret position calculation.", iae);
            }
            tf.requestFocus();
        }
    }
}

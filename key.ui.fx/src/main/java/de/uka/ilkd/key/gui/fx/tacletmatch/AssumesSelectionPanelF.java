/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.tacletmatch;

import java.util.ArrayList;
import java.util.List;
import javafx.animation.PauseTransition;
import javafx.collections.FXCollections;
import javafx.collections.ObservableList;
import javafx.geometry.Insets;
import javafx.geometry.Pos;
import javafx.scene.Node;
import javafx.scene.control.Label;
import javafx.scene.control.ListCell;
import javafx.scene.control.ListView;
import javafx.scene.control.RadioButton;
import javafx.scene.control.TextArea;
import javafx.scene.control.ToggleGroup;
import javafx.scene.control.Tooltip;
import javafx.scene.layout.HBox;
import javafx.scene.layout.Priority;
import javafx.scene.layout.VBox;
import javafx.util.Duration;

import de.uka.ilkd.key.control.instantiation_model.TacletAssumesModel;
import de.uka.ilkd.key.control.instantiation_model.TacletInstantiationModel;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.nparser.KeyIO;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.proof.io.ProofSaver;

import org.key_project.prover.rules.instantiation.AssumesFormulaInstantiation;
import org.key_project.prover.sequent.Sequent;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.util.parsing.Position;

/**
 * Lets the user instantiate the taclet's {@code \assumes} sequent in one of two ways, chosen with a
 * toggle:
 * <ul>
 * <li><b>Select from sequent</b> &ndash; per assumes formula, pick a matching sequent formula from
 * a list (sequent-view-like);</li>
 * <li><b>Type the {@code \assumes} sequent</b> &ndash; type the whole instantiated assumes sequent
 * (antecedent {@code ==>} succedent). It is checked incrementally: parse/syntax of the sequent, the
 * expected number of formulas, and &ndash; via the dialog status &ndash; whether it is compatible
 * with the existing schema-variable bindings.</li>
 * </ul>
 *
 * <p>
 * Port of {@code de.uka.ilkd.key.gui.tacletmatch.AssumesSelectionPanel}
 * (AssumesSelectionPanel.java:
 * 44-457). Event semantics preserved: the select card is a per-formula {@link ListView} writing
 * each selection straight into the model (AssumesSelectionPanel.java:169-174); the manual card's
 * two editors validate debounced on change (the Swing 300&nbsp;ms {@code Timer} becomes a
 * {@link PauseTransition}, AssumesSelectionPanel.java:263-274); a parse error highlights the
 * offending character (a selection in the corresponding editor replaces the Swing highlighter
 * painting, AssumesSelectionPanel.java:398-411).
 */
class AssumesSelectionPanelF extends VBox {

    /** abbreviate candidate text longer than this in the list (full text on hover) */
    private static final int ABBREV_LIMIT = 200;

    /** debounce of the manual editor's incremental validation */
    private static final Duration VALIDATE_DEBOUNCE = Duration.millis(300);

    private final TacletInstantiationModel model;
    private final Services services;
    private final NotationInfo notationInfo;
    private final Runnable onChange;

    private final int anteSize;
    private final int count;

    /** per-formula combo models (index 0..anteSize-1 antecedent, rest succedent) */
    private final TacletAssumesModel[] choices;
    /** the "Manual Input" sentinel of each combo model */
    private final AssumesFormulaInstantiation[] sentinels;
    /** the candidate lists, one per assumes formula (select mode) */
    private final List<ListView<AssumesFormulaInstantiation>> lists = new ArrayList<>();

    private final VBox selectCard = new VBox(4);
    private final VBox manualCard = new VBox(4);
    private final TextArea anteArea = new TextArea();
    private final TextArea succArea = new TextArea();
    private final Label manualStatus = new Label(" ");

    private boolean manualMode;
    private PauseTransition debounce;

    AssumesSelectionPanelF(TacletInstantiationModel model, Services services,
            NotationInfo notationInfo, Runnable onChange) {
        this.model = model;
        this.services = services;
        this.notationInfo = notationInfo;
        this.onChange = onChange;

        Sequent assumes = model.application().taclet().assumesSequent();
        this.anteSize = assumes.antecedent().size();
        this.count = model.ifChoiceModelCount();

        this.choices = new TacletAssumesModel[count];
        this.sentinels = new AssumesFormulaInstantiation[count];
        for (int i = 0; i < count; i++) {
            choices[i] = model.ifChoiceModel(i);
            sentinels[i] = choices[i].getElementAt(choices[i].getSize() - 1);
        }

        VBox section = TmStyleF.section("Assumptions (\\assumes)");
        section.getChildren().addAll(buildToggle(), selectCard, manualCard);
        getChildren().add(section);

        showSelect();
    }

    /**
     * the two-way toggle between the select and the manual card (AssumesSelectionPanel.java:111)
     */
    private Node buildToggle() {
        RadioButton selectBtn = new RadioButton("Select from sequent");
        RadioButton manualBtn = new RadioButton("Type the \\assumes sequent");
        ToggleGroup group = new ToggleGroup();
        group.getToggles().addAll(selectBtn, manualBtn);
        group.selectToggle(selectBtn);
        selectBtn.setOnAction(e -> showSelect());
        manualBtn.setOnAction(e -> showManual());

        HBox row = new HBox(8, selectBtn, manualBtn);
        row.setAlignment(Pos.CENTER_LEFT);
        return row;
    }

    private void buildSelectCard() {
        selectCard.getChildren().clear();
        lists.clear();
        for (int i = 0; i < count; i++) {
            selectCard.getChildren().add(buildFormulaSelector(i));
        }
    }

    /**
     * one per assumes formula: the schematic formula as header, then the matching sequent formulas
     * to choose from (AssumesSelectionPanel.java:139-189).
     */
    private Node buildFormulaSelector(int index) {
        VBox p = new VBox(4);
        p.setPadding(new Insets(4, 0, 8, 0));

        HBox header = new HBox(6);
        header.setAlignment(Pos.CENTER_LEFT);
        header.getChildren().addAll(TmStyleF.muted((index < anteSize ? "antecedent" : "succedent")
            + ":"), new ExpandableTextF(ProofSaver.printAnything(model.ifFma(index), services)));
        p.getChildren().add(header);

        List<AssumesFormulaInstantiation> candidates = new ArrayList<>();
        for (int k = 0; k < choices[index].getSize() - 1; k++) {
            candidates.add(choices[index].getElementAt(k));
        }
        ObservableList<AssumesFormulaInstantiation> lm = FXCollections.observableList(candidates);
        ListView<AssumesFormulaInstantiation> list = new ListView<>(lm);
        list.setCellFactory(lv -> new ListCell<>() {
            @Override
            protected void updateItem(AssumesFormulaInstantiation item, boolean empty) {
                super.updateItem(item, empty);
                setText(empty || item == null ? null
                        : TmTextF.collapseToLine(text(item),
                            ABBREV_LIMIT));
                setTooltip(empty || item == null ? null : new Tooltip(text(item)));
                getStyleClass().add(TmStyleF.MONO_CLASS);
            }
        });
        list.getSelectionModel().selectedItemProperty().addListener((obs, oldV, newV) -> {
            if (newV != null && !manualMode) {
                choices[index].setSelectedItem(newV);
                onChange.run();
            }
        });
        lists.add(list);

        if (lm.isEmpty()) {
            Label none =
                TmStyleF.muted("(no matching formula — use \"Type the \\assumes sequent\")");
            p.getChildren().add(none);
        } else {
            list.setPrefHeight(Math.min(Math.max(lm.size(), 1), 4) * 24 + 10);
            p.getChildren().add(list);
            list.getSelectionModel().select(selectedIndexOf(index, candidates));
        }
        return p;
    }

    private int selectedIndexOf(int index, List<AssumesFormulaInstantiation> lm) {
        Object selected = choices[index].getSelectedItem();
        for (int k = 0; k < lm.size(); k++) {
            if (lm.get(k) == selected) {
                return k;
            }
        }
        return 0;
    }

    private Node buildManualCard() {
        HBox guide = new HBox(6);
        guide.setAlignment(Pos.CENTER_LEFT);
        guide.getChildren().addAll(TmStyleF.muted("schematic"),
            new ExpandableTextF(schematicSequent()));

        HBox editor = new HBox(8, labeledArea("antecedent", anteArea), new Label("  ⟹  "),
            labeledArea("succedent", succArea));
        editor.setAlignment(Pos.CENTER_LEFT);
        HBox.setHgrow(anteArea, Priority.ALWAYS);
        HBox.setHgrow(succArea, Priority.ALWAYS);

        anteArea.textProperty().addListener((obs, o, n) -> scheduleValidation());
        succArea.textProperty().addListener((obs, o, n) -> scheduleValidation());

        manualCard.getChildren().addAll(guide, editor, manualStatus);
        return manualCard;
    }

    /** a labelled, monospaced, wrapping editor (AssumesSelectionPanel.java:250-261) */
    private Node labeledArea(String label, TextArea area) {
        area.getStyleClass().add(TmStyleF.MONO_CLASS);
        area.setWrapText(true);
        area.setPrefRowCount(4);
        VBox p = new VBox(2, TmStyleF.muted(label), area);
        VBox.setVgrow(area, Priority.ALWAYS);
        return p;
    }

    /** debounces the manual validation (AssumesSelectionPanel.java:263-274) */
    private void scheduleValidation() {
        if (!manualMode) {
            return;
        }
        if (debounce == null) {
            debounce = new PauseTransition(VALIDATE_DEBOUNCE);
            debounce.setOnFinished(e -> validateManual());
        }
        debounce.playFromStart();
    }

    private void showSelect() {
        manualMode = false;
        buildSelectCard();
        manualCard.setVisible(false);
        manualCard.setManaged(false);
        selectCard.setVisible(true);
        selectCard.setManaged(true);
        for (int i = 0; i < count; i++) {
            AssumesFormulaInstantiation v =
                i < lists.size() ? lists.get(i).getSelectionModel().getSelectedItem() : null;
            if (v != null) {
                choices[i].setSelectedItem(v);
            }
            model.setManualInput(i, "");
        }
        onChange.run();
    }

    private void showManual() {
        manualMode = true;
        selectCard.setVisible(false);
        selectCard.setManaged(false);
        manualCard.setVisible(true);
        manualCard.setManaged(true);
        if (manualCard.getChildren().isEmpty()) {
            buildManualCard();
        }
        validateManual();
    }

    /**
     * parses and checks the typed assumes sequent, then feeds it to the per-formula models so the
     * dialog status reflects compatibility with the existing bindings
     * (AssumesSelectionPanel.java:300-346).
     */
    private void validateManual() {
        clearErrorHighlights();
        String ante = anteArea.getText();
        String succ = succArea.getText();
        if (ante.isBlank() && succ.isBlank()) {
            status(WarnKind.WARN, "● waiting for the \\assumes sequent…");
            clearManual();
            onChange.run();
            return;
        }

        Sequent parsed;
        try {
            parsed = new KeyIO(services).parseSequent(AssumesInputF.combined(ante, succ));
        } catch (Exception e) {
            reportSyntaxError(e);
            clearManual();
            onChange.run();
            return;
        }

        String arity = AssumesInputF.arityError(parsed.antecedent().size(),
            parsed.succedent().size(), anteSize, count - anteSize);
        if (arity != null) {
            status(WarnKind.ERROR, "✗ " + arity);
            clearManual();
            onChange.run();
            return;
        }

        int i = 0;
        for (SequentFormula sf : parsed.antecedent()) {
            applyManual(i++, sf);
        }
        for (SequentFormula sf : parsed.succedent()) {
            applyManual(i++, sf);
        }

        // compatibility with the existing bindings is reflected by the model status
        AssumesInputF.ModelStatus st = AssumesInputF.classify(model.getStatusString());
        if (st.kind() == AssumesInputF.StatusKind.OK) {
            status(WarnKind.OK, "✓ " + st.text());
        } else {
            status(WarnKind.WARN, "● " + st.text());
        }
        onChange.run();
    }

    private void applyManual(int index, SequentFormula sf) {
        choices[index].setSelectedItem(sentinels[index]);
        model.setManualInput(index, ProofSaver.printAnything(sf.formula(), services));
    }

    private void clearManual() {
        // keep the model in "manual" selection so an empty/invalid editor reads as incomplete
        // rather than silently falling back to the select-mode candidate
        for (int i = 0; i < count; i++) {
            choices[i].setSelectedItem(sentinels[i]);
            model.setManualInput(i, "");
        }
    }

    /** writes the current input back to the model (selections are applied live) */
    public void pushAllInputToModel() {
        if (manualMode) {
            validateManual();
        } else {
            showSelect();
        }
    }

    /** status kinds rendered with themed colours (Swing's fixed OK/WARN/ERROR colours) */
    private enum WarnKind {
        OK, WARN, ERROR
    }

    private void status(WarnKind kind, String text) {
        manualStatus.setText(text);
        manualStatus.getStyleClass().removeAll("tacletmatch-status-ok", "tacletmatch-status-warn",
            "tacletmatch-status-error");
        manualStatus.getStyleClass()
                .add(switch (kind) {
                    case OK -> "tacletmatch-status-ok";
                    case WARN -> "tacletmatch-status-warn";
                    case ERROR -> "tacletmatch-status-error";
                });
    }

    /**
     * reports a parse failure: a clean message (without the noisy " at &lt;pos&gt;"/"unknown") and,
     * if the failure carries a location, a highlight at the offending position in the editor
     * (AssumesSelectionPanel.java:380-396).
     */
    private void reportSyntaxError(Throwable e) {
        AssumesInputF.SyntaxError err = AssumesInputF.extract(e);
        status(WarnKind.ERROR, "✗ " + err.message());

        Position pos = err.position();
        if (pos != null) {
            String combined = AssumesInputF.combined(anteArea.getText(), succArea.getText());
            int off = TmTextF.offsetOf(combined, pos.line(), pos.column());
            AssumesInputF.Target target = AssumesInputF.locate(anteArea.getText(), off);
            // a position inside the synthetic "==>" separator belongs to neither editor
            if (target.side() == AssumesInputF.Side.ANTECEDENT) {
                highlightAt(anteArea, target.offset());
            } else if (target.side() == AssumesInputF.Side.SUCCEDENT) {
                highlightAt(succArea, target.offset());
            }
        }
    }

    /**
     * highlights the offending character: the Swing highlighter painting becomes a selection of
     * that single character in the editor (which the themes render as a highlight).
     */
    private static void highlightAt(TextArea area, int offset) {
        int len = area.getText().length();
        int start = Math.max(0, Math.min(offset, len));
        int end = Math.min(start + 1, len);
        if (start == end && start > 0) {
            start = end - 1;
        }
        if (end > start) {
            area.selectRange(start, end);
        }
        area.requestFocus();
    }

    private void clearErrorHighlights() {
        anteArea.deselect();
        succArea.deselect();
    }

    private String schematicSequent() {
        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < anteSize; i++) {
            if (i > 0) {
                sb.append(", ");
            }
            sb.append(TmPrintF.term(services, notationInfo, model.ifFma(i)));
        }
        sb.append("  ==>  ");
        for (int i = anteSize; i < count; i++) {
            if (i > anteSize) {
                sb.append(", ");
            }
            sb.append(TmPrintF.term(services, notationInfo, model.ifFma(i)));
        }
        return sb.toString();
    }

    private String text(AssumesFormulaInstantiation inst) {
        SequentFormula sf = inst.getSequentFormula();
        return sf != null ? TmPrintF.term(services, notationInfo, sf.formula()) : inst.toString();
    }

    /** whether the manual card is currently active (used by the verification driver) */
    boolean isManualMode() {
        return manualMode;
    }
}

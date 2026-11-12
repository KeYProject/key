/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.tacletmatch;

import javafx.geometry.Pos;
import javafx.scene.Node;
import javafx.scene.Scene;
import javafx.scene.control.Label;
import javafx.scene.control.ScrollPane;
import javafx.scene.control.Tab;
import javafx.scene.control.TabPane;
import javafx.scene.control.Tooltip;
import javafx.scene.layout.BorderPane;
import javafx.scene.layout.HBox;
import javafx.scene.layout.Priority;
import javafx.scene.layout.VBox;
import javafx.stage.Stage;

import de.uka.ilkd.key.control.ProofControl;
import de.uka.ilkd.key.control.instantiation_model.TacletInstantiationModel;
import de.uka.ilkd.key.gui.fx.fonticons.FontAwesomeSolid;
import de.uka.ilkd.key.gui.fx.fonticons.IconFactoryF;
import de.uka.ilkd.key.gui.fx.theme.ThemeManager;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.proof.Goal;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Dialog for completing and applying an interactively selected taclet.
 *
 * <p>
 * Per instantiation alternative it shows a {@link MatchInfoPanelF} (how the find matched and the
 * bindings it determined), an {@link SVInstantiationPanelF} (the schema variables left to
 * instantiate), an {@link AssumesSelectionPanelF} (choose or type the {@code \assumes}
 * instantiation) and a {@link ResultPreviewPanelF} (the resulting sequents). The inputs and the
 * preview are laid out in a {@link ResponsiveSplitF} that collapses to tabs when the window is
 * narrow.
 *
 * <p>
 * Port of {@code de.uka.ilkd.key.gui.tacletmatch.TacletMatchDialog}
 * (TacletMatchDialog.java:39-383).
 * Deviations from the Swing original: the dialog is centred on the owner stage instead of the
 * sequent-beside placement heuristic (TacletMatchDialog.java:103-150 — that heuristic reads the
 * Swing goal view's screen bounds; the FX docking layout can be re-queried once the rule-menu
 * integration lands), and the window-geometry preferences are not persisted (the FX configuration
 * store has no per-dialog preference registry yet). In-place highlighting of each schema variable
 * inside the matched term is a planned follow-up in Swing as well (TacletMatchDialog.java:37).
 */
public class TacletMatchDialogF extends ApplyTacletDialogF {

    private static final Logger LOGGER = LoggerFactory.getLogger(TacletMatchDialogF.class);

    private final Services services;
    private final NotationInfo notationInfo;

    /** one schema-variable instantiation panel per instantiation alternative */
    private final SVInstantiationPanelF[] svPanels;

    /**
     * the assumptions panel per alternative, or {@code null} if the taclet has no assumes
     */
    private final AssumesSelectionPanelF[] ifPanels;

    /** the result preview panel per alternative */
    private final ResultPreviewPanelF[] previews;

    /** the match info panel per alternative (for the self test's highlight assertion) */
    private final MatchInfoPanelF[] matchPanels;

    /** the tabbed pane selecting between instantiation alternatives */
    private TabPane alternatives;

    /** single-line footer status (icon + message) */
    private final Label statusLabel = new Label(" ");

    public TacletMatchDialogF(Stage owner, TacletInstantiationModel[] model, Goal goal,
            ProofControl proofControl, Services services, NotationInfo notationInfo) {
        super(owner, "Choose Taclet Instantiation", model, proofControl, goal);
        this.services = services;
        this.notationInfo = notationInfo;
        this.svPanels = new SVInstantiationPanelF[model.length];
        this.ifPanels = new AssumesSelectionPanelF[model.length];
        this.previews = new ResultPreviewPanelF[model.length];
        this.matchPanels = new MatchInfoPanelF[model.length];

        for (TacletInstantiationModel aModel : model) {
            aModel.prepareUnmatchedInstantiation();
        }

        BorderPane root = new BorderPane();
        root.setCenter(createInstantiationPanel());
        root.setBottom(createFooter());

        Scene scene = new Scene(root, 1000, 620);
        // style the dialog scene with the active theme stylesheet (like every other FX window;
        // the classic completion dialog does the same) — without it the dialog would render in
        // plain Modena regardless of the light/dark theme
        ThemeManager.getInstance().style(scene);
        root.setMinSize(640, 400);
        setScene(scene);
        if (owner != null) {
            centerOnOwner(owner);
        }
        show();
        LOGGER.debug("TacletMatchDialogF opened for {}", model[0].taclet().name());
    }

    private void centerOnOwner(Stage owner) {
        setX(Math.max(0, owner.getX() + (owner.getWidth() - getWidth()) / 2));
        setY(Math.max(0, owner.getY() + (owner.getHeight() - getHeight()) / 3));
    }

    /**
     * builds the instantiation area: the single alternative's content directly, or a tab strip
     * selecting between the alternatives (TacletMatchDialog.java:158-170).
     */
    private javafx.scene.Node createInstantiationPanel() {
        if (model.length == 1) {
            // single match: show its content directly, no tab strip
            return buildAlternative(0);
        }

        alternatives = new TabPane();
        for (int i = 0; i < model.length; i++) {
            alternatives.getTabs().add(new Tab("Match " + (i + 1), buildAlternative(i)));
        }
        alternatives.setTabClosingPolicy(TabPane.TabClosingPolicy.UNAVAILABLE);
        alternatives.getSelectionModel().selectedItemProperty()
                .addListener((obs, oldTab, newTab) -> refreshStatus(current()));
        return alternatives;
    }

    /**
     * a compact footer: status icon + message on the left, cancel/apply on the right
     * (TacletMatchDialog.java:172-191).
     */
    private javafx.scene.Node createFooter() {
        statusLabel.setAlignment(Pos.CENTER_LEFT);
        HBox buttons = new HBox(8, applyButton, cancelButton);
        buttons.setAlignment(Pos.CENTER_RIGHT);

        HBox footer = new HBox(12, statusLabel, buttons);
        footer.getStyleClass().add("tacletmatch-footer");
        footer.setAlignment(Pos.CENTER_LEFT);
        footer.setPadding(new javafx.geometry.Insets(10, 12, 10, 12));
        HBox.setHgrow(statusLabel, Priority.ALWAYS);
        HBox.setHgrow(buttons, Priority.NEVER);

        setStatus(model[current()].getStatusString());
        applyButton.setOnAction(e -> handleApply());
        return footer;
    }

    /**
     * builds the instantiation content (match overview, schema variables, assumptions, preview) for
     * one instantiation alternative (TacletMatchDialog.java:197-234).
     */
    private javafx.scene.Node buildAlternative(int i) {
        // inputs: match overview, schema variables, assumptions
        VBox inputs = new VBox(4);

        MatchInfoPanelF matchPanel = new MatchInfoPanelF(model[i], services, notationInfo);
        matchPanels[i] = matchPanel;
        inputs.getChildren().add(matchPanel);

        SVInstantiationPanelF svPanel =
            new SVInstantiationPanelF(model[i], services, notationInfo, () -> refreshStatus(i));
        svPanels[i] = svPanel;
        inputs.getChildren().add(svPanel);

        if (!model[i].application().taclet().assumesSequent().isEmpty()) {
            AssumesSelectionPanelF assumes =
                new AssumesSelectionPanelF(model[i], services, notationInfo,
                    () -> refreshStatus(i));
            ifPanels[i] = assumes;
            inputs.getChildren().add(assumes);
        }

        // preview, on the other side of the split
        VBox previewPane = new VBox(4);
        ResultPreviewPanelF preview =
            new ResultPreviewPanelF(model[i], services, notationInfo, goal);
        previews[i] = preview;
        previewPane.getChildren().add(preview);

        ScrollPane inputsScroll = scroll(inputs);
        ScrollPane previewScroll = scroll(previewPane);
        return new ResponsiveSplitF(inputsScroll, "Instantiate", previewScroll, "Result preview");
    }

    /** a vertical-scrolling, width-filling scroll pane (TacletMatchDialog.java:228-234) */
    private static ScrollPane scroll(VBox view) {
        ScrollPane scroll = new ScrollPane(view);
        scroll.setBorder(null);
        scroll.setFitToWidth(true);
        return scroll;
    }

    /**
     * refreshes the status display and result preview from the given alternative if selected
     * (TacletMatchDialog.java:282-290).
     */
    private void refreshStatus(int idx) {
        if (idx == current()) {
            setStatus(model[idx].getStatusString());
            if (previews[idx] != null) {
                previews[idx].requestUpdate();
            }
        }
    }

    @Override
    public void setStatus(String s) {
        if (s == null || s.isEmpty()) {
            statusLabel.setText(" ");
            statusLabel.setGraphic(null);
            statusLabel.setTooltip(null);
            return;
        }
        int nl = s.indexOf('\n');
        String firstLine = nl >= 0 ? s.substring(0, nl) : s;

        FontAwesomeSolid glyph;
        String colorClass;
        if (s.startsWith("Instantiation is OK")) {
            glyph = FontAwesomeSolid.CHECK_CIRCLE;
            colorClass = "tacletmatch-status-ok";
        } else if (s.startsWith("Rule is not applicable")) {
            glyph = FontAwesomeSolid.TIMES_CIRCLE;
            colorClass = "tacletmatch-status-error";
        } else {
            glyph = FontAwesomeSolid.EXCLAMATION_CIRCLE;
            colorClass = "tacletmatch-status-warn";
        }
        Node icon = IconFactoryF.createIcon(glyph, 14);
        icon.getStyleClass().add(colorClass);
        statusLabel.setGraphic(icon);
        statusLabel.setText(firstLine);
        statusLabel.getStyleClass().removeAll("tacletmatch-status-ok", "tacletmatch-status-warn",
            "tacletmatch-status-error");
        statusLabel.getStyleClass().add(colorClass);
        statusLabel.setTooltip(nl >= 0 ? new Tooltip(s) : null);
    }

    @Override
    protected int current() {
        return alternatives == null ? 0 : alternatives.getSelectionModel().getSelectedIndex();
    }

    @Override
    protected void pushAllInputToModel() {
        int i = current();
        if (ifPanels[i] != null) {
            ifPanels[i].pushAllInputToModel();
        }
        if (svPanels[i] != null) {
            svPanels[i].pushAllInputToModel();
        }
    }

    // ------------------------------------------------------------------
    // self-test hooks (package-private; used by TacletMatchVerifyF)
    // ------------------------------------------------------------------

    /** programmatically presses the apply button (the same handler as its onAction) */
    void fireApply() {
        applyButton.fire();
    }

    /** programmatically presses the cancel button (the same handler as its onAction) */
    void fireCancel() {
        cancelButton.fire();
    }

    /** the current status line text as displayed (first line only) */
    String statusText() {
        return statusLabel.getText();
    }

    /** the schema-variable panel of alternative {@code i} */
    SVInstantiationPanelF svPanel(int i) {
        return svPanels[i];
    }

    /** the assumptions panel of alternative {@code i}, or {@code null} */
    AssumesSelectionPanelF assumesPanel(int i) {
        return ifPanels[i];
    }

    /** the number of schema-variable spans highlighted in alternative {@code i}'s matched term */
    int highlightSpanCount(int i) {
        return matchPanels[i] == null ? 0 : matchPanels[i].getHighlightSpanCount();
    }

    /** the preview panel of alternative {@code i}, or {@code null} */
    ResultPreviewPanelF preview(int i) {
        return previews[i];
    }
}

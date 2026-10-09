/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.join;

import java.util.ArrayList;
import java.util.List;
import javafx.collections.FXCollections;
import javafx.geometry.Insets;
import javafx.geometry.Pos;
import javafx.scene.Scene;
import javafx.scene.control.Button;
import javafx.scene.control.Label;
import javafx.scene.control.ListCell;
import javafx.scene.control.ListView;
import javafx.scene.control.ScrollPane;
import javafx.scene.control.SelectionMode;
import javafx.scene.control.Tooltip;
import javafx.scene.layout.BorderPane;
import javafx.scene.layout.HBox;
import javafx.scene.layout.Priority;
import javafx.scene.layout.Region;
import javafx.scene.layout.VBox;
import javafx.stage.Modality;
import javafx.stage.Stage;
import javafx.stage.Window;

import de.uka.ilkd.key.gui.fx.join.DecisionPredicateInputF.InspectorF;
import de.uka.ilkd.key.gui.fx.join.DecisionPredicateInputF.ListenerF;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.delayedcut.ApplicationCheck;
import de.uka.ilkd.key.proof.delayedcut.DelayedCut;
import de.uka.ilkd.key.proof.delayedcut.DelayedCutProcessor;
import de.uka.ilkd.key.proof.join.LateApplicationCheck;
import de.uka.ilkd.key.proof.join.PredicateEstimator;
import de.uka.ilkd.key.proof.join.PredicateEstimator.Result;
import de.uka.ilkd.key.proof.join.ProspectivePartner;

import org.key_project.prover.sequent.Sequent;

/**
 * The dialog of the interactive "delayed cut" join rule. Counter-part of
 * {@code de.uka.ilkd.key.gui.join.JoinDialog} in the Swing module {@code key.ui}
 * (JoinDialog.java:33-375): after the user has chosen two compatible join partners and confirmed
 * with an edited decision predicate, the caller starts the join processor with the selected
 * partner ({@link JoinActionF}).
 * <p>
 * Ported behavior (Swing evidence):
 * <ul>
 * <li>headline "Join Goal &lt;serialNr&gt;" plus the sequent of the first partner node
 * (JoinDialog.java:150-153);</li>
 * <li>a single-selection list of prospective partners ("Goal &lt;serialNr&gt;"); selecting an
 * entry shows its sequent, its estimated common predicate and the "true for goal A / false for
 * goal B" info label (JoinDialog.java:157-183, :185-197);</li>
 * <li>per-partner applicability via {@code LateApplicationCheck} with a
 * {@code NoNewSymbolsCheck} on both partner nodes (JoinDialog.java:165-173);</li>
 * <li>a checked predicate input ({@link DecisionPredicateInputF}) whose validity drives the OK
 * button (JoinDialog.java:43, :132-141) — OK is enabled iff the input is a valid formula
 * <em>and</em> the selected partner is applicable;</li>
 * <li>a details/info box that shows either the "new symbols" inapplicability notice, the
 * validation reason, or "Join is applicable." in green (JoinDialog.java:48-53, :257-274);</li>
 * <li>on OK the caller reads {@link #getSelectedPartner()}; the selected partner carries the
 * (edited) common predicate (JoinDialog.java:133-135).</li>
 * </ul>
 * Deviations: JavaFX {@code Stage} built in code, messages styled via CSS classes instead of
 * {@code Color}s, and the click-to-popup behavior of the Swing {@code ClickableMessageBox}
 * becomes a click-to-alert on the message (JoinDialog.java:296-297).
 */
public final class JoinDialogF {

    /**
     * The inapplicability notice shown for partners that cannot be joined because new symbols
     * were introduced on the branches (Swing JoinDialog.INFO, JoinDialog.java:48-53).
     */
    private static final String INFO = """
            It is not possible to join both goals, because new symbols have been introduced
             on the branches which belong to the goals: Up to now the treatment of new symbols
            is not supported by the joining mechanism.

            """;

    private final Stage stage = new Stage();
    private final ContentPanel content;
    private final Button okButton = new Button("OK");

    private boolean okButtonHasBeenPressed = false;

    /**
     * Creates a non-modal-configured join dialog (shown modally by {@link #show(Window)}).
     *
     * @param partnerList the prospective join partners (Swing parameter of the same name)
     * @param proof the underlying proof
     * @param estimator the decision predicate estimator ({@code PredicateEstimator.STD_ESTIMATOR}
     *        in the Swing caller)
     * @param services the proof services
     */
    public JoinDialogF(List<ProspectivePartner> partnerList, Proof proof,
            PredicateEstimator estimator, Services services) {
        this(partnerList, proof, estimator, services, null);
    }

    public JoinDialogF(List<ProspectivePartner> partnerList, Proof proof,
            PredicateEstimator estimator, Services services, Window owner) {
        stage.setTitle("Joining");
        okButton.setDisable(true);
        okButton.setDefaultButton(true);
        okButton.setTooltip(new Tooltip("Apply the join with the edited decision predicate."));
        // Swing JoinDialog.java:42-43: the input listener drives the OK button enablement
        content = new ContentPanel(partnerList, proof, estimator,
            (input, valid, reason) -> okButton.setDisable(!valid), services);

        Button cancelButton = new Button("Cancel");
        cancelButton.setCancelButton(true);
        cancelButton.setOnAction(e -> stage.close());
        okButton.setOnAction(e -> {
            okButtonHasBeenPressed = true;
            stage.close();
        });
        Region spacer = new Region();
        HBox.setHgrow(spacer, Priority.ALWAYS);
        HBox buttonBar = new HBox(5, spacer, okButton, cancelButton);
        buttonBar.setAlignment(Pos.CENTER_RIGHT);
        buttonBar.setPadding(new Insets(5, 8, 8, 8));

        BorderPane root = new BorderPane(content, null, null, buttonBar, null);
        root.setPadding(new Insets(8));
        Scene scene = new Scene(root, 860, 640);
        de.uka.ilkd.key.gui.fx.theme.ThemeManager.getInstance().style(scene);
        stage.setScene(scene);
        stage.initModality(Modality.APPLICATION_MODAL);
        if (owner != null) {
            stage.initOwner(owner);
        }
    }

    /** Shows the dialog and blocks until it is closed (the Swing dialog is modal, too). */
    public void show(Window owner) {
        if (owner != null && stage.getOwner() == null) {
            stage.initOwner(owner);
        }
        stage.showAndWait();
    }

    // joinmerge: test support for the key.fx.verify.joinmerge self test — non-blocking show and
    // programmatic OK/cancel with the same semantics as the buttons; the production path uses
    // show(Window).

    /** Shows the dialog without blocking (self-test support; parity with {@link #show(Window)}). */
    public void showNonBlocking() {
        stage.show();
    }

    /** Confirms the dialog if the OK button is enabled (self-test support). */
    public void requestOk() {
        if (!okButton.isDisabled()) {
            okButtonHasBeenPressed = true;
            stage.close();
        }
    }

    /** Cancels the dialog (self-test support; parity with the Swing cancel button). */
    public void requestCancel() {
        stage.close();
    }

    /** Exposes the dialog stage for tests. */
    public Stage getStageForVerification() {
        return stage;
    }

    /** Swing StdDialog.okButtonHasBeenPressed. */
    public boolean okButtonHasBeenPressed() {
        return okButtonHasBeenPressed;
    }

    /**
     * The partner selected in the choice list, carrying the (edited) common predicate (Swing
     * JoinDialog.getSelectedPartner, JoinDialog.java:368-371).
     */
    public ProspectivePartner getSelectedPartner() {
        return content.getSelectedPartner();
    }

    /** Exposes the OK button for tests. */
    public Button getOkButton() {
        return okButton;
    }

    /** Exposes the partner choice list for tests. */
    public ListView<ContentItem> getChoiceList() {
        return content.getChoiceList();
    }

    /** Exposes the predicate input for tests. */
    public DecisionPredicateInputF getPredicateInput() {
        return content.getPredicateInput();
    }

    /** Exposes the info box for tests (last message text or {@code null}). */
    public Label getLastInfoMessage() {
        return content.getLastInfoMessage();
    }

    /** Exposes the sequent viewer of the selected partner for tests. */
    public SequentViewerF getSequentViewer2() {
        return content.getSequentViewer2();
    }

    /**
     * One selectable entry of the choice list (Swing ContentItem, JoinDialog.java:73-120).
     */
    public static final class ContentItem {

        final ProspectivePartner partner;
        final InspectorF inspector;
        final boolean applicable;

        public ContentItem(ProspectivePartner partner, Services services, boolean applicable) {
            this.partner = partner;
            this.inspector = new InspectorForDecisionPredicatesF(services,
                partner.getCommonParent(), DelayedCut.DECISION_PREDICATE_IN_ANTECEDENT,
                DelayedCutProcessor.getApplicationChecks());
            this.applicable = applicable;
        }

        public InspectorF getInspector() {
            return inspector;
        }

        public boolean isApplicable() {
            return applicable;
        }

        Sequent getSequent() {
            return partner.getNode(1).sequent();
        }

        @Override
        public String toString() {
            return "Goal " + partner.getNode(1).serialNr();
        }

        public String getPredicateInfo() {
            return "Decision Formula (true for Goal " + partner.getNode(0).serialNr()
                + ", false for Goal " + partner.getNode(1).serialNr() + ")";
        }

        public String getPredicate(Proof proof) {
            if (partner.getCommonPredicate() == null) {
                return "";
            }
            LogicPrinter printer =
                LogicPrinter.purePrinter(new NotationInfo(), proof.getServices());
            printer.printTerm(partner.getCommonPredicate());
            return printer.result();
        }
    }

    /**
     * The dialog content (Swing ContentPanel, JoinDialog.java:56-366): headline with sequent of
     * the first partner, "with" separator, partner choice list with sequent viewer, predicate
     * info label, checked predicate input and the details info box.
     */
    private final class ContentPanel extends VBox {

        private final SequentViewerF sequentViewer1 = new SequentViewerF();
        private final SequentViewerF sequentViewer2 = new SequentViewerF();
        private final ListView<ContentItem> choiceList = new ListView<>();
        private final DecisionPredicateInputF predicateInput = new DecisionPredicateInputF();
        private final Label infoPredicate = new Label(" ");
        private final MessageBoxF infoBox = new MessageBoxF();
        private final Label headline = new Label("Join");
        private final Label lastInfoMessage = new Label();

        private final Proof proof;
        private final PredicateEstimator estimator;
        private final Services services;

        ContentPanel(List<ProspectivePartner> partnerList, Proof proof,
                PredicateEstimator estimator, ListenerF validListener, Services services) {
            this.proof = proof;
            this.estimator = estimator;
            this.services = services;

            headline.getStyleClass().add("dialog-section-title");
            infoPredicate.getStyleClass().add("join-predicate-info");
            choiceList.setCellFactory(view -> new ListCell<>() {
                @Override
                protected void updateItem(ContentItem item, boolean empty) {
                    super.updateItem(item, empty);
                    setText(empty || item == null ? null : item.toString());
                }
            });
            choiceList.setPrefWidth(110);
            choiceList.setPrefHeight(280);
            sequentViewer1.setPrefSize(380, 240);
            sequentViewer2.setPrefSize(300, 240);
            infoBox.setPrefHeight(90);
            VBox.setVgrow(infoBox, Priority.ALWAYS);
            infoBox.getStyleClass().add("join-details-box");

            // Swing JoinDialog.java:132-141 — the input listener stores the edited predicate on
            // the selected partner and forwards validity (with the partner's applicability
            // factored in) to the dialog's OK-button listener.
            predicateInput.addListener((input, valid, reason) -> {
                if (valid) {
                    getSelectedPartner().setCommonPredicate(
                        // the Swing code uses InspectorForFormulas.translate here
                        // (JoinDialog.java:134-135), which is the same KeyIO translation
                        InspectorForDecisionPredicatesF.translate(services, input));
                    validListener.userInputChanged(input, getSelectedItem() != null
                            && getSelectedItem().isApplicable(),
                        reason);
                } else {
                    validListener.userInputChanged(input, false, reason);
                }
                refreshInfoBox(reason);
            });

            choiceList.getSelectionModel().setSelectionMode(SelectionMode.SINGLE);
            choiceList.getSelectionModel().selectedItemProperty().addListener((obs, oldV, newV) -> {
                int index = choiceList.getSelectionModel().getSelectedIndex();
                if (index >= 0) {
                    selectionChanged(index);
                }
            });

            // layout (Swing JoinDialog.create, JoinDialog.java:207-255)
            VBox leftBox = new VBox(4, headline, new ScrollPane(sequentViewer1));
            VBox.setVgrow(leftBox, Priority.ALWAYS);
            Label withLabel = new Label("with");
            withLabel.getStyleClass().add("join-with-label");
            HBox rightRow = new HBox(5, choiceList, new ScrollPane(sequentViewer2));
            HBox.setHgrow(rightRow, Priority.ALWAYS);
            VBox rightBox = new VBox(4, withLabel, rightRow);
            VBox.setVgrow(rightBox, Priority.ALWAYS);
            HBox.setHgrow(leftBox, Priority.ALWAYS);
            HBox.setHgrow(rightBox, Priority.ALWAYS);
            HBox partnersBox = new HBox(10, leftBox, rightBox);
            VBox.setVgrow(partnersBox, Priority.ALWAYS);

            ScrollPane infoBoxPane = new ScrollPane(infoBox);
            infoBoxPane.setFitToWidth(true);
            infoBoxPane.setPrefHeight(100);

            setSpacing(5);
            getChildren().addAll(partnersBox, infoPredicate, predicateInput, infoBoxPane);

            if (partnerList != null && !partnerList.isEmpty()) {
                fill(partnerList);
            }
        }

        /**
         * Swing ContentPanel.fill (JoinDialog.java:150-183): estimate the decision predicates,
         * compute the applicability with a {@code NoNewSymbolsCheck} on both partner nodes, and
         * preselect the first partner.
         */
        private void fill(List<ProspectivePartner> partnerList) {
            Node node = partnerList.get(0).getNode(0);
            headline.setText("Join Goal " + node.serialNr());
            sequentViewer1.setSequent(node.sequent(), proof.getServices());

            List<ContentItem> model = new ArrayList<>();
            for (ProspectivePartner partner : partnerList) {
                Result result = estimator.estimate(partner, proof);
                partner.setCommonPredicate(result.getPredicate());
                partner.setCommonParent(result.getCommonParent());

                ApplicationCheck check = new ApplicationCheck.NoNewSymbolsCheck();

                boolean applicable = true;
                applicable = LateApplicationCheck.INSTANCE
                        .check(partner.getNode(0), result.getCommonParent(), check).isEmpty()
                        && applicable;
                applicable = LateApplicationCheck.INSTANCE
                        .check(partner.getNode(1), result.getCommonParent(), check).isEmpty()
                        && applicable;

                model.add(new ContentItem(partner, services, applicable));
            }

            choiceList.setItems(FXCollections.observableList(model));
            choiceList.getSelectionModel().selectFirst();
        }

        /**
         * Swing ContentPanel.selectionChanged (JoinDialog.java:185-197): show the partner
         * sequent, its predicate and the predicate info label.
         */
        private void selectionChanged(int index) {
            ContentItem item = choiceList.getItems().get(index);
            sequentViewer2.setSequent(item.getSequent(), proof.getServices());
            predicateInput.setInspector(item.getInspector());
            predicateInput.setInput(item.getPredicate(proof));
            infoPredicate.setText(item.getPredicateInfo());
        }

        /**
         * Swing ContentPanel.refreshInfoBox (JoinDialog.java:257-274): inapplicability notice,
         * red validation reason ("reason#detail" convention) or green "Join is applicable.".
         */
        private void refreshInfoBox(String reason) {
            ContentItem item = getSelectedItem();
            infoBox.clear();
            if (item == null) {
                return;
            }
            if (!item.isApplicable()) {
                lastInfoMessage.setText("Goal " + item.partner.getNode(0).serialNr() + " and "
                    + "Goal " + item.partner.getNode(1).serialNr() + " cannot be joined.");
                infoBox.add(INFO, lastInfoMessage.getText(), true);
            } else if (reason != null) {
                String[] segments = reason.split("#");
                lastInfoMessage.setText(segments[0]);
                infoBox.add(segments.length > 1 ? segments[1] : null, segments[0], true);
            } else {
                lastInfoMessage.setText("Join is applicable.");
                infoBox.add(null, lastInfoMessage.getText(), false);
            }
        }

        ContentItem getSelectedItem() {
            return choiceList.getSelectionModel().getSelectedItem();
        }

        ProspectivePartner getSelectedPartner() {
            ContentItem item = getSelectedItem();
            return item == null ? null : item.partner;
        }

        ListView<ContentItem> getChoiceList() {
            return choiceList;
        }

        DecisionPredicateInputF getPredicateInput() {
            return predicateInput;
        }

        Label getLastInfoMessage() {
            return lastInfoMessage;
        }

        SequentViewerF getSequentViewer2() {
            return sequentViewer2;
        }
    }

    /**
     * Minimal port of the Swing {@code ClickableMessageBox} (used by the join dialog at
     * JoinDialog.java:65-66, :289-301): a vertical list of colored message labels; clicking a
     * message opens an information alert with the (optional) long detail text, mirroring the
     * Swing "Problem Description" dialog (JoinDialog.java:296-297).
     */
    private static final class MessageBoxF extends VBox {

        MessageBoxF() {
            setSpacing(2);
        }

        void clear() {
            getChildren().clear();
        }

        /**
         * Adds a message.
         *
         * @param detail long text shown on click (may be {@code null})
         * @param text the message text
         * @param error whether the message is an error (red) or a success (green) message
         */
        void add(String detail, String text, boolean error) {
            Label label = new Label(text);
            // "join-message-row" is pre-staged in key-light/key-dark.css for this port; the
            // error/success classes style the text with -key-error/-key-success (appended CSS)
            label.getStyleClass().addAll("join-message-row",
                error ? "message-error" : "message-ok");
            label.setWrapText(true);
            if (detail != null && !detail.isBlank()) {
                label.setOnMouseClicked(e -> {
                    javafx.scene.control.Alert alert =
                        new javafx.scene.control.Alert(
                            javafx.scene.control.Alert.AlertType.INFORMATION, detail);
                    alert.setHeaderText("Problem Description");
                    alert.initOwner(getScene() == null ? null : getScene().getWindow());
                    alert.show();
                });
            }
            getChildren().add(label);
        }
    }
}

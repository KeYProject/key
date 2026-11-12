/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.dialogs;

import java.io.File;
import java.nio.file.Path;
import java.util.List;
import java.util.Optional;
import javafx.collections.FXCollections;
import javafx.geometry.Insets;
import javafx.geometry.Pos;
import javafx.scene.Scene;
import javafx.scene.control.Button;
import javafx.scene.control.ButtonBar;
import javafx.scene.control.ButtonType;
import javafx.scene.control.CheckBox;
import javafx.scene.control.Label;
import javafx.scene.control.ListView;
import javafx.scene.control.TextArea;
import javafx.scene.input.KeyCode;
import javafx.scene.layout.BorderPane;
import javafx.scene.layout.HBox;
import javafx.scene.layout.Priority;
import javafx.scene.layout.VBox;
import javafx.stage.FileChooser;
import javafx.stage.Modality;
import javafx.stage.Stage;
import javafx.stage.Window;

import de.uka.ilkd.key.gui.fx.theme.ThemeManager;
import de.uka.ilkd.key.settings.ProofIndependentSettings;

/**
 * lemma (P2b, A3): full JavaFX port of the Swing {@code LoadUserTacletsDialog}
 * (key.ui lemmatagenerator/LoadUserTacletsDialog.java, 499 lines), opened by the
 * "Load User Defined Taclets…" entry and the "Prove" submenu's "Load User Defined Taclets for
 * Proving" entry. The dialog collects
 * <ul>
 * <li>the (single) file containing the user-defined taclets (Swing
 * {@code UserTacletFileBox}),</li>
 * <li>the list of <em>axiom files</em> (Swing {@code axiomsList} + Add/Remove buttons, enabled
 * in PROVE mode while proof obligations are generated; the axioms are only loaded for the
 * lemmata, not for the current proof),</li>
 * <li>the "Generate proof obligations for taclets" checkbox (Swing {@code getLemmaCheckBox},
 * default {@code true}): un-checking requires the confirmation dialog of the Swing
 * {@code InfoDialog} ("the calculus will become unsound"), remembered via
 * {@code LemmaGeneratorSettings.showingDialogUsingAxioms},</li>
 * <li>the "Help" window with the Swing {@code HELP_TEXT}.</li>
 * </ul>
 */
public final class LoadUserTacletsDialogF {

    /**
     * The two modes of the Swing dialog ({@code LoadUserTacletsDialog.Mode}): PROVE only creates
     * the proof obligations, LOAD additionally loads the taclets into the current proof (the
     * axiom panel is only enabled in PROVE mode — Swing {@code enableAxiomFilePanel}).
     */
    public enum Mode {
        PROVE, LOAD
    }

    /**
     * The collected choices of the dialog.
     *
     * @param fileForTaclets the {@code .key} file with the user-defined taclets
     *        (Swing {@code getFileForTaclets()})
     * @param generateProofObligations whether a soundness proof obligation should be created for
     *        each taclet (Swing {@code isGenerateProofObligations()})
     * @param filesForAxioms the axiom files (Swing {@code getFilesForAxioms()}; empty in LOAD
     *        mode or without proof obligations)
     */
    public record Result(Path fileForTaclets, boolean generateProofObligations,
            List<Path> filesForAxioms) {
    }

    /** Swing {@code HELP_TEXT} (LoadUserTacletsDialog.java:35-50). */
    private static final String HELP_TEXT =
        """
                In this dialog you can choose the files that are used for loading user-defined taclets:

                User-Defined Taclets:
                This file contains the taclets that should be loaded, so that they can be used for the current proof. For each taclet an extra proof obligation is built that must be provable, in order to sustain the correctness of the calculus.

                Definitions:
                This file contains the signature (function symbols, predicate symbols, sorts) that are used for creating the proof obligations mentioned above. In most cases it should be the same file as indicated in 'User-Defined Taclets'.

                Axioms:
                In order to prove the correctness of the created lemmata, for some user-defined taclets the introduction of additional axioms is necessary. At this point you can add them.
                Beware of the fact that it is crucial for the correctness of the calculus that the used axioms are consistent.It is the responsibility of the user to guarantee this consistency.

                Technical Remarks:
                The axioms must be stored in another file than the user-defined taclets. Furthermore the axioms are only loaded for the lemmata, but not for the current proof.""";

    /** Swing {@code INFO_TEXT} (LoadUserTacletsDialog.java:52-56). */
    private static final String INFO_TEXT = """
            Be aware of the fact that you are going to load taclets
            without creating corresponding proof obligations!
            In case that the taclets that you want to load are unsound,
            the calculus will become unsound!""";

    private LoadUserTacletsDialogF() {
    }

    /**
     * Shows the modal taclet-loading dialog.
     *
     * @param owner the owner window (the main window stage), may be {@code null}
     * @param mode PROVE or LOAD
     * @return the chosen file, checkbox state and axiom files, or {@link Optional#empty()} when
     *         canceled (Swing {@code showAsDialog()} returns {@code false})
     */
    public static Optional<Result> showDialog(Window owner, Mode mode) {
        Stage dialog = new Stage();
        dialog.setTitle(
            mode == Mode.LOAD ? "Load User-Defined Taclets" : "Prove User-Defined Taclets");
        dialog.initOwner(owner);
        if (owner != null) {
            // Swing: JDialog(parent, title, modal) — window-modal
            dialog.initModality(Modality.WINDOW_MODAL);
        }

        Label hint = new Label("Choose the file containing the user-defined taclets."
            + (mode == Mode.LOAD
                    ? "\nEach taclet is loaded for the current proof when its proof obligation"
                        + " can be proven."
                    : "\nFor each taclet a proof obligation is created."));
        hint.setWrapText(true);

        Label chosen = new Label("");
        chosen.setWrapText(true);

        Button choose = new Button("Choose…");
        Button ok = new Button("OK");
        ok.setDefaultButton(true);
        ok.setDisable(true); // enabled once a file has been chosen (Swing fileHasBeenChosen)
        choose.setOnAction(e -> {
            FileChooser chooser = new FileChooser();
            chooser.setTitle("Choose the file with the user-defined taclets");
            // Swing KeYFileChooser opens with the last chosen directory
            chooser.getExtensionFilters()
                    .add(new FileChooser.ExtensionFilter("KeY files (*.key)", "*.key"));
            File selected = chooser.showOpenDialog(dialog);
            if (selected != null) {
                chosen.setText(selected.getPath());
                ok.setDisable(false);
            }
        });

        // lemma: the axiom-file list (Swing axiomsList + getAdd/RemoveAxiomFileButton,
        // LoadUserTacletsDialog.java:245-249, :315-338) — enabled in PROVE mode while proof
        // obligations are generated
        ListView<Path> axiomsList = new ListView<>(FXCollections.observableArrayList());
        axiomsList.setPrefHeight(90);
        axiomsList.getStyleClass().add("axioms-list");
        Button addAxiomFileButton = new Button("Add axiom file…");
        Button removeAxiomFileButton = new Button("Remove");
        removeAxiomFileButton.disableProperty()
                .bind(axiomsList.getSelectionModel().selectedItemProperty().isNull());
        addAxiomFileButton.setOnAction(e -> {
            FileChooser chooser = new FileChooser();
            chooser.setTitle("Choose the file with the axioms");
            chooser.getExtensionFilters()
                    .add(new FileChooser.ExtensionFilter("KeY files (*.key)", "*.key"));
            File selected = chooser.showOpenDialog(dialog);
            if (selected != null && !axiomsList.getItems().contains(selected.toPath())) {
                axiomsList.getItems().add(selected.toPath());
            }
        });
        removeAxiomFileButton.setOnAction(
            e -> axiomsList.getItems().remove(axiomsList.getSelectionModel().getSelectedItem()));
        TitledPaneAxioms axiomPanel =
            new TitledPaneAxioms(axiomsList, addAxiomFileButton, removeAxiomFileButton);

        CheckBox lemmaBox = new CheckBox("Generate proof obligations for taclets");
        lemmaBox.setSelected(true);
        // lemma: the Swing warning on un-checking (getLemmaCheckBox, :203-237): re-check, show
        // the InfoDialog confirmation (unless suppressed) and only then really un-check
        lemmaBox.setOnAction(e -> {
            if (lemmaBox.isSelected()) {
                axiomPanel.setVisible(true);
                return;
            }
            lemmaBox.setSelected(true);
            boolean showDialogUsingAxioms = ProofIndependentSettings.DEFAULT_INSTANCE
                    .getLemmaGeneratorSettings().isShowingDialogUsingAxioms();
            InfoDialogResult answer = showInfoDialog(dialog, INFO_TEXT, showDialogUsingAxioms);
            if (answer.confirmed()) {
                lemmaBox.setSelected(false);
                axiomPanel.setVisible(false);
                axiomsList.getItems().clear();
                ProofIndependentSettings.DEFAULT_INSTANCE.getLemmaGeneratorSettings()
                        .setShowDialogUsingAxioms(
                            showDialogUsingAxioms && answer.showNextTime());
            }
        });
        // LOAD mode: the axiom panel is disabled (Swing enableAxiomFilePanel(false), :258-263)
        if (mode == Mode.LOAD) {
            lemmaBox.setDisable(true);
            axiomPanel.setVisible(false);
        }

        Button helpButton = new Button("Help");
        helpButton.setOnAction(e -> showHelpWindow(dialog));
        Button cancel = new Button("Cancel");
        ButtonBar.setButtonData(ok, ButtonBar.ButtonData.OK_DONE);
        ButtonBar.setButtonData(cancel, ButtonBar.ButtonData.CANCEL_CLOSE);
        ButtonBar buttons = new ButtonBar();
        buttons.getButtons().addAll(ok, cancel, helpButton);

        VBox center = new VBox(10, hint, choose, chosen, lemmaBox, axiomPanel);
        center.setPadding(new Insets(12));
        BorderPane root = new BorderPane();
        root.setCenter(center);
        root.setBottom(buttons);
        BorderPane.setMargin(buttons, new Insets(10));
        Scene scene = new Scene(root, 560, 360);
        ThemeManager.getInstance().manage(scene);
        scene.setOnKeyPressed(e -> {
            if (e.getCode() == KeyCode.ESCAPE) {
                dialog.close();
                e.consume();
            }
        });
        dialog.setScene(scene);

        Result[] result = new Result[1];
        ok.setOnAction(e -> {
            List<Path> axioms =
                lemmaBox.isSelected() && mode == Mode.PROVE ? List.copyOf(axiomsList.getItems())
                        : List.of();
            result[0] = new Result(Path.of(chosen.getText()), lemmaBox.isSelected(), axioms);
            dialog.close();
        });
        cancel.setOnAction(e -> dialog.close());
        dialog.showAndWait();
        return Optional.ofNullable(result[0]);
    }

    /** The axiom-panel row: the list between the Add and Remove buttons. */
    private static final class TitledPaneAxioms extends VBox {
        TitledPaneAxioms(ListView<Path> axiomsList, Button add, Button remove) {
            super(6);
            Label title = new Label("Axioms (only loaded for the lemmata, not for the proof)");
            title.getStyleClass().add("axioms-title");
            HBox row = new HBox(6, axiomsList, new VBox(6, add, remove));
            HBox.setHgrow(axiomsList, Priority.ALWAYS);
            row.setAlignment(Pos.CENTER_LEFT);
            getChildren().addAll(title, row);
            setPadding(new Insets(4));
            getStyleClass().add("axioms-panel");
        }
    }

    /** The Swing {@code InfoDialog} answer (confirmed + "don't show this dialog again"). */
    private record InfoDialogResult(boolean confirmed, boolean showNextTime) {
    }

    /**
     * The Swing {@code InfoDialog} (lemmatagenerator/InfoDialog.java): the given text, the
     * "Don't show this dialog again." checkbox and OK/Cancel.
     */
    private static InfoDialogResult showInfoDialog(Window owner, String text,
            boolean withCheckbox) {
        javafx.scene.control.Dialog<ButtonType> info = new javafx.scene.control.Dialog<>();
        info.setTitle("Info");
        info.setHeaderText(null);
        VBox content = new VBox(8, new Label(text));
        content.setPadding(new Insets(10));
        CheckBox dontShow = new CheckBox("Don't show this dialog again.");
        dontShow.setSelected(true);
        if (withCheckbox) {
            content.getChildren().add(dontShow);
        }
        info.getDialogPane().setContent(content);
        info.getDialogPane().getButtonTypes().addAll(ButtonType.OK, ButtonType.CANCEL);
        if (owner != null) {
            info.initOwner(owner);
        }
        Optional<ButtonType> answer = info.showAndWait();
        boolean confirmed = answer.isPresent() && answer.get() == ButtonType.OK;
        return new InfoDialogResult(confirmed, dontShow.isSelected());
    }

    /** The Swing help window (getHelpWindow, LoadUserTacletsDialog.java:270-287). */
    private static void showHelpWindow(Window owner) {
        Stage help = new Stage();
        help.setTitle("Help");
        TextArea text = new TextArea(HELP_TEXT);
        text.setEditable(false);
        text.setWrapText(true);
        help.setScene(new Scene(text, 500, 400));
        if (owner != null) {
            help.initOwner(owner);
        }
        help.show();
    }
}

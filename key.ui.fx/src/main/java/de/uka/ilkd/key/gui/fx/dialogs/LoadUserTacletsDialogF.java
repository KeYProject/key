/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.dialogs;

import java.io.File;
import java.nio.file.Path;
import java.util.Optional;
import javafx.geometry.Insets;
import javafx.scene.Scene;
import javafx.scene.control.Button;
import javafx.scene.control.ButtonBar;
import javafx.scene.control.CheckBox;
import javafx.scene.control.Label;
import javafx.scene.input.KeyCode;
import javafx.scene.layout.BorderPane;
import javafx.scene.layout.VBox;
import javafx.stage.FileChooser;
import javafx.stage.Modality;
import javafx.stage.Window;

import de.uka.ilkd.key.gui.fx.theme.ThemeManager;

/**
 * menu: MP5 — JavaFX port of the Swing {@code LoadUserTacletsDialog}
 * (key.ui/.../gui/lemmatagenerator/LoadUserTacletsDialog.java), opened by the
 * "Load User Defined Taclets…" entry and the "Prove" submenu's "Load User Defined Taclets for
 * Proving" entry. The dialog collects
 * <ul>
 * <li>the (single) file containing the user-defined taclets — the Swing dialog additionally
 * maintains a list of <em>axiom files</em> ({@code Mode.PROVE} axiom panel / the LOAD mode's
 * justification box); the axiom-file list is deliberately not ported
 * ({@code TacletSoundnessPOLoader} then simply never loads axioms), marked {@code // menu:}
 * KNOWN-DEFERRED below,</li>
 * <li>the "Generate proof obligations for taclets" checkbox (Swing
 * {@code getLemmaCheckBox}, default {@code true}): when un-checked the taclets are loaded
 * without a soundness proof.</li>
 * </ul>
 */
public final class LoadUserTacletsDialogF {

    /**
     * The two modes of the Swing dialog ({@code LoadUserTacletsDialog.Mode}): PROVE only creates
     * the proof obligations, LOAD additionally loads the taclets into the current proof.
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
     */
    public record Result(Path fileForTaclets, boolean generateProofObligations) {
    }

    private LoadUserTacletsDialogF() {
    }

    /**
     * Shows the modal taclet-loading dialog.
     *
     * @param owner the owner window (the main window stage), may be {@code null}
     * @param mode PROVE or LOAD
     * @return the chosen file and checkbox state, or {@link Optional#empty()} when canceled
     *         (Swing {@code showAsDialog()} returns {@code false})
     */
    public static Optional<Result> showDialog(Window owner, Mode mode) {
        javafx.stage.Stage dialog = new javafx.stage.Stage();
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

        CheckBox lemmaBox = new CheckBox("Generate proof obligations for taclets");
        lemmaBox.setSelected(true);
        // menu: the Swing warning on un-checking (InfoDialog "you are going to load taclets
        // without creating corresponding proof obligations") is dropped — the checkbox state
        // is persisted nowhere in the FX port.
        lemmaBox.setWrapText(true);

        Button cancel = new Button("Cancel");
        ButtonBar.setButtonData(ok, ButtonBar.ButtonData.OK_DONE);
        ButtonBar.setButtonData(cancel, ButtonBar.ButtonData.CANCEL_CLOSE);
        ButtonBar buttons = new ButtonBar();
        buttons.getButtons().addAll(ok, cancel);

        VBox center = new VBox(10, hint, choose, chosen, lemmaBox);
        center.setPadding(new Insets(12));
        BorderPane root = new BorderPane();
        root.setCenter(center);
        root.setBottom(buttons);
        BorderPane.setMargin(buttons, new Insets(10));
        Scene scene = new Scene(root, 520, 210);
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
            result[0] = new Result(Path.of(chosen.getText()), lemmaBox.isSelected());
            dialog.close();
        });
        cancel.setOnAction(e -> dialog.close());
        dialog.showAndWait();
        return Optional.ofNullable(result[0]);
    }
}

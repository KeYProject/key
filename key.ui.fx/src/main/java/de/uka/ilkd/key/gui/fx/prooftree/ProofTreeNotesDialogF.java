/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.prooftree;

import javafx.geometry.Insets;
import javafx.geometry.Pos;
import javafx.scene.Scene;
import javafx.scene.control.Button;
import javafx.scene.control.Label;
import javafx.scene.control.TextArea;
import javafx.scene.layout.BorderPane;
import javafx.scene.layout.HBox;
import javafx.stage.Modality;
import javafx.stage.Stage;

import de.uka.ilkd.key.gui.fx.theme.ThemeManager;
import de.uka.ilkd.key.proof.Node;

import org.key_project.util.javafx.FxUtil;

/**
 * prooftree (P3a, C23): JavaFX port of the Swing "Edit Notes..." popup of the proof tree
 * ({@code ProofTreePopupFactory.Notes}): a small text editor for the free-form note attached to
 * a proof node ({@code NodeInfo.setNotes}). Empty input clears the note, cancel leaves it
 * untouched — the Swing {@code JOptionPane.showInputDialog} semantics, as a plain window instead
 * of a modal option pane (same adaptation as the other P2b/P3 dialogs).
 */
public final class ProofTreeNotesDialogF {

    private final Stage stage = new Stage();
    private final Node node;
    /** The note text field (package-visible for the {@code key.fx.verify.prooftree} harness). */
    final TextArea textArea = new TextArea();

    /**
     * @param original the current note of the node, may be {@code null}
     * @param node the proof node whose note is edited
     */
    public ProofTreeNotesDialogF(String original, Node node) {
        this.node = node;
        textArea.setPromptText("Attach a note to this proof node...");
        textArea.setText(original == null ? "" : original);
        textArea.getStyleClass().addAll("proof-tree-notes-area");

        Label nodeLabel = new Label("Annotate proof node " + node.serialNr()
            + (node.getAppliedRuleApp() != null ? " (" + node.getAppliedRuleApp().rule().name()
                + ")" : ""));
        nodeLabel.getStyleClass().add("proof-tree-notes-title");

        Button okButton = new Button("OK");
        okButton.setDefaultButton(true);
        okButton.setOnAction(e -> requestOk());
        Button cancelButton = new Button("Cancel");
        cancelButton.setCancelButton(true);
        cancelButton.setOnAction(e -> requestCancel());
        HBox buttons = new HBox(8, okButton, cancelButton);
        buttons.setAlignment(Pos.CENTER_RIGHT);
        buttons.setPadding(new Insets(6));

        BorderPane root = new BorderPane();
        root.setTop(nodeLabel);
        root.setCenter(textArea);
        root.setBottom(buttons);
        BorderPane.setMargin(nodeLabel, new Insets(6, 6, 0, 6));
        BorderPane.setMargin(textArea, new Insets(6));

        Scene scene = new Scene(root, 480, 240);
        ThemeManager.getInstance().style(scene);
        stage.setTitle("Annotate this proof node");
        stage.setScene(scene);
        stage.setMinWidth(300);
        stage.setMinHeight(160);
    }

    /** Shows the dialog non-blocking (P3a harness seam like the P2b configurators). */
    public void showNonBlocking() {
        if (!FxUtil.isFxThread()) {
            FxUtil.runLater(this::showNonBlocking);
            return;
        }
        stage.initModality(Modality.NONE);
        stage.show();
    }

    /**
     * OK: stores the note on the node — empty input clears it, exactly like the Swing dialog
     * (ProofTreePopupFactory.Notes.actionPerformed).
     */
    public void requestOk() {
        String text = textArea.getText();
        if (text == null || text.isEmpty()) {
            node.getNodeInfo().setNotes(null);
        } else {
            node.getNodeInfo().setNotes(text);
        }
        stage.close();
    }

    /** Cancel: closes without changing the note (Swing returns {@code null}). */
    public void requestCancel() {
        stage.close();
    }

    /** @return the stage (verification harness) */
    public Stage getStage() {
        return stage;
    }
}

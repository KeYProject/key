/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.notification;

import java.util.ArrayList;
import java.util.List;
import javafx.geometry.Insets;
import javafx.geometry.Pos;
import javafx.scene.Scene;
import javafx.scene.control.Button;
import javafx.scene.control.Label;
import javafx.scene.control.ScrollPane;
import javafx.scene.layout.Priority;
import javafx.scene.layout.VBox;

import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.Statistics;

import org.key_project.util.collection.Pair;

/**
 * A small non-modal window informing the user about a closed proof together with its final
 * statistics.
 * <p>
 * Port of the proof-closed display action of the Swing notification framework: {@code
 * ProofClosedJTextPaneDisplay} (actions/ProofClosedJTextPaneDisplay.java) opens the
 * {@code ShowProofStatistics.Window} ("Proof Statistics" dialog) for the closed proof. The FX
 * port shows the same summary ({@link Statistics#getSummary()} plus the open-goal count) in a
 * plain {@link VBox}; unlike Swing the window is not styled with the proof-tree font.
 */
public final class ProofClosedDialogF extends javafx.stage.Stage {

    /** the currently open proof-closed dialogs (self-test hook, see {@link #anyShowing()}) */
    private static final List<ProofClosedDialogF> OPEN_DIALOGS = new ArrayList<>();

    private ProofClosedDialogF(Proof proof) {
        setTitle("Proof closed");
        setResizable(false);

        Statistics stats = proof.getStatistics();
        int openGoals = proof.openGoals().size();

        Label header = new Label("Proof " + proof.name() + " closed successfully.");
        header.getStyleClass().add("notification-dialog-header");
        header.setWrapText(true);
        header.setMaxWidth(360);

        VBox statsBox = new VBox(4);
        statsBox.getChildren().add(new Label("Open goals: " + openGoals));
        List<Pair<String, String>> summary = stats.getSummary();
        if (summary != null) {
            for (Pair<String, String> entry : summary) {
                if ("".equals(entry.second)) {
                    statsBox.getChildren().add(new Label(entry.first));
                } else {
                    statsBox.getChildren().add(new Label(entry.first + ": " + entry.second));
                }
            }
        }

        Button close = new Button("Close");
        close.setOnAction(e -> hide());
        VBox.setVgrow(close, Priority.NEVER);

        ScrollPane scroll = new ScrollPane(statsBox);
        scroll.setFitToWidth(true);
        scroll.setPrefViewportHeight(Math.min(240, 40 + 22 * statsBox.getChildren().size()));

        VBox root = new VBox(12, header, scroll, close);
        root.getStyleClass().add("notification-dialog");
        root.setPadding(new Insets(14));
        root.setAlignment(Pos.CENTER_LEFT);

        Scene scene = new Scene(root, 380, Math.min(480, 160 + 22 * statsBox.getChildren().size()));
        setScene(scene);
    }

    /**
     * Shows the proof-closed dialog for the given proof (Swing parity:
     * {@code ProofClosedJTextPaneDisplay.execute} opens the statistics window for the closed
     * proof). The dialog is non-modal, like the Swing {@code ShowProofStatistics.Window}.
     *
     * @param proof the closed proof, must not be {@code null}
     */
    public static void show(Proof proof) {
        ProofClosedDialogF dialog = new ProofClosedDialogF(proof);
        OPEN_DIALOGS.add(dialog);
        dialog.setOnHidden(e -> OPEN_DIALOGS.remove(dialog));
        dialog.show();
    }

    /**
     * @return whether any proof-closed dialog is currently visible (self-test hook used by
     *         {@code key.fx.verify.notifications})
     */
    static boolean anyShowing() {
        return OPEN_DIALOGS.stream().anyMatch(javafx.stage.Stage::isShowing);
    }
}

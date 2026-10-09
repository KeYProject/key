/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.notification;

import java.util.List;
import javafx.geometry.Insets;
import javafx.geometry.Pos;
import javafx.scene.Scene;
import javafx.scene.control.Button;
import javafx.scene.control.Label;
import javafx.scene.control.ScrollPane;
import javafx.scene.layout.Priority;
import javafx.scene.layout.VBox;
import javafx.stage.Window;

import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.Statistics;

import org.key_project.util.collection.Pair;

/**
 * menu: non-modal window showing the statistics of the selected proof (Swing
 * {@code ShowProofStatistics.Window}, ShowProofStatistics.java:234-410): the open-goal count plus
 * the {@link Statistics#getSummary()} pairs, exactly the layout built by the FX
 * {@link ProofClosedDialogF} ({@code ProofClosedJTextPaneDisplay} opens the same Swing
 * "Proof Statistics" window for closed proofs).
 * <p>
 * The plain VBox/ScrollPane layout replaces the Swing HTML table; no export buttons for now
 * (the CSV/HTML export of {@code ShowProofStatistics.Window} is not ported).
 */
public final class ProofStatisticsDialogF extends javafx.stage.Stage {

    private ProofStatisticsDialogF(Window owner, Proof proof) {
        setTitle("Proof Statistics");
        if (owner != null) {
            initOwner(owner);
        }

        Statistics stats = proof.getStatistics();
        int openGoals = proof.openGoals().size();

        VBox statsBox = new VBox(4);
        statsBox.getChildren().add(new Label("Open goals: " + openGoals));
        // menu: Swing getHTMLStatisticsMessage iterates the summary; a null summary is rendered
        // gracefully (Swing would NPE — defensive here)
        List<Pair<String, String>> summary = stats == null ? null : stats.getSummary();
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

        VBox root = new VBox(12, new Label("Proof " + proof.name()), scroll, close);
        root.getStyleClass().add("notification-dialog");
        root.setPadding(new Insets(14));
        root.setAlignment(Pos.CENTER_LEFT);

        Scene scene = new Scene(root, 380, Math.min(480, 180 + 22 * statsBox.getChildren().size()));
        setScene(scene);
    }

    /**
     * Shows the statistics window for the given proof (Swing
     * {@code ShowProofStatistics.actionPerformed}, ShowProofStatistics.java:69-78: non-modal
     * {@code Window}, like the proof-closed dialog).
     *
     * @param owner the owner window (the main window stage); may be {@code null}
     * @param proof the selected proof, must not be {@code null} (the menu item is disabled
     *        without a proof)
     */
    public static void show(Window owner, Proof proof) {
        ProofStatisticsDialogF dialog = new ProofStatisticsDialogF(owner, proof);
        dialog.show();
    }
}

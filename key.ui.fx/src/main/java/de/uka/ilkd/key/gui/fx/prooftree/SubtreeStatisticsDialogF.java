/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.prooftree;

import java.util.Iterator;
import java.util.Map.Entry;
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
import de.uka.ilkd.key.proof.Statistics;
import de.uka.ilkd.key.proof.reference.ClosedBy;

import org.key_project.util.collection.Pair;
import org.key_project.util.javafx.FxUtil;

/**
 * prooftree (P3a, C23): JavaFX port of the Swing "Show Subtree Statistics" popup of the proof
 * tree ({@code ProofTreePopupFactory.SubtreeStatistics} → {@code ShowProofStatistics}):
 * displays the open/cached goals of the invoked node's subtree and the rule-application
 * statistics of that subtree.
 * <p>
 * <b>KNOWN-SIMPLIFIED:</b> the Swing report is an HTML-styled window with Save buttons
 * (HTML/CSV export); the FX port shows the same numbers as plain text. The export is tracked as
 * audit item A4 (P3c) — see PARITY-SIGNOFF.md.
 */
public final class SubtreeStatisticsDialogF {

    private final Stage stage = new Stage();

    /**
     * @param node the proof node whose subtree statistics are shown (the popup's invoked node)
     */
    public SubtreeStatisticsDialogF(Node node) {
        TextArea report = new TextArea(renderReport(node));
        report.setEditable(false);
        report.setWrapText(false);
        report.getStyleClass().add("subtree-stats-area");

        Label title = new Label("Subtree statistics for node " + node.serialNr() + ":"
            + node.name());
        title.getStyleClass().add("subtree-stats-title");

        Button closeButton = new Button("Close");
        closeButton.setDefaultButton(true);
        closeButton.setOnAction(e -> requestOk());
        HBox buttons = new HBox(8, closeButton);
        buttons.setAlignment(Pos.CENTER_RIGHT);
        buttons.setPadding(new Insets(6));

        BorderPane root = new BorderPane();
        root.setTop(title);
        root.setCenter(report);
        root.setBottom(buttons);
        BorderPane.setMargin(title, new Insets(6, 6, 0, 6));
        BorderPane.setMargin(report, new Insets(6));

        Scene scene = new Scene(root, 520, 420);
        ThemeManager.getInstance().style(scene);
        stage.setTitle("Subtree Statistics");
        stage.setScene(scene);
        stage.setMinWidth(320);
        stage.setMinHeight(240);
    }

    /**
     * Renders the statistics text, mirroring Swing {@code ShowProofStatistics}:
     * {@code getHTMLStatisticsMessage(node)} counts the open and cached goals of the subtree,
     * {@code Statistics.getSummary()} lists the rule-application counters. Package-visible for
     * the {@code key.fx.verify.prooftree} harness.
     */
    static String renderReport(Node node) {
        int openGoals = 0;
        int cachedGoals = 0;
        // Swing quirk preserved: the ClosedBy lookup is tested on the invoked node (not the
        // leaf), so all open leaves count as cached when the node itself is a cached cutting
        // point (ShowProofStatistics.getHTMLStatisticsMessage, actions/ShowProofStatistics.java)
        Iterator<Node> leaves = node.leavesIterator();
        while (leaves.hasNext()) {
            Node leaf = leaves.next();
            if (node.proof().getOpenGoal(leaf) != null) {
                if (node.lookup(ClosedBy.class) != null) {
                    cachedGoals++;
                } else {
                    openGoals++;
                }
            }
        }
        StringBuilder sb = new StringBuilder();
        String line = System.lineSeparator();
        sb.append("Subtree of node ").append(node.serialNr()).append(':')
                .append(node.name()).append(line);
        sb.append(line).append("Open goals: ").append(openGoals).append(line);
        sb.append("Cached goals: ").append(cachedGoals).append(line);
        Statistics statistics = node.statistics();
        StringBuilder details = new StringBuilder();
        for (Pair<String, String> summary : statistics.getSummary()) {
            if (summary.second == null || summary.second.isEmpty()) {
                details.append(summary.first).append(line);
            } else {
                details.append(summary.first).append(": ").append(summary.second).append(line);
            }
        }
        if (!statistics.getInteractiveAppsDetails().isEmpty()) {
            details.append(line).append("Interactive rule application details:").append(line);
            for (Entry<String, Integer> entry : statistics.getInteractiveAppsDetails().entrySet()) {
                details.append("  ").append(entry.getKey()).append(": ").append(entry.getValue())
                        .append(line);
            }
        }
        if (details.isEmpty()) {
            details.append("(no rule application statistics for this node)").append(line);
        }
        sb.append(details);
        return sb.toString();
    }

    /** Shows the dialog non-blocking (P3a harness seam). */
    public void showNonBlocking() {
        if (!FxUtil.isFxThread()) {
            FxUtil.runLater(this::showNonBlocking);
            return;
        }
        stage.initModality(Modality.NONE);
        stage.show();
    }

    /** Closes the dialog as if the Close button had been pressed (verification harness). */
    public void requestOk() {
        stage.close();
    }

    /** @return the stage (verification harness) */
    public Stage getStage() {
        return stage;
    }
}

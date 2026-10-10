/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.notification;

import java.io.BufferedWriter;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.SortedSet;
import java.util.TreeSet;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import javafx.geometry.Insets;
import javafx.geometry.Pos;
import javafx.scene.Scene;
import javafx.scene.control.Button;
import javafx.scene.control.Label;
import javafx.scene.control.ScrollPane;
import javafx.scene.layout.HBox;
import javafx.scene.layout.Priority;
import javafx.scene.layout.VBox;
import javafx.stage.FileChooser;
import javafx.stage.Window;

import de.uka.ilkd.key.gui.fx.notification.NotificationManagerF.Kind;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.Statistics;
import de.uka.ilkd.key.proof.reference.ClosedBy;
import de.uka.ilkd.key.util.MiscTools;

import org.key_project.util.collection.Pair;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * menu: non-modal window showing the statistics of the selected proof (Swing
 * {@code ShowProofStatistics.Window}, ShowProofStatistics.java:234-410): the open-goal count plus
 * the {@link Statistics#getSummary()} pairs, exactly the layout built by the FX
 * {@link ProofClosedDialogF} ({@code ProofClosedJTextPaneDisplay} opens the same Swing
 * "Proof Statistics" window for closed proofs).
 * <p>
 * Export (A4, P3c): the Swing CSV/HTML export of {@code ShowProofStatistics.Window} is ported —
 * the "Export as CSV" / "Export as HTML" buttons write the exact Swing formats
 * ({@link #getCSVStatisticsMessage(Proof)} / {@link #getHTMLStatisticsMessage(Proof)}) to a file
 * chosen with a {@link FileChooser}; the plain VBox/ScrollPane layout of the dialog itself
 * replaces the Swing HTML table (KNOWN-SIMPLIFIED, the exported HTML keeps the Swing format).
 */
public final class ProofStatisticsDialogF extends javafx.stage.Stage {

    private static final Logger LOGGER = LoggerFactory.getLogger(ProofStatisticsDialogF.class);

    /**
     * Regex pattern to check for tooltips in statistics entries (Swing
     * {@code ShowProofStatistics.TOOLTIP_PATTERN}).
     */
    private static final Pattern TOOLTIP_PATTERN = Pattern.compile(".+\\[tooltip: (.+)]");

    private static final String CSV_SEPARATOR = ";";

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

        // A4 (P3c): the export buttons of Swing ShowProofStatistics.Window (:299-307) — the
        // Swing save buttons "Export as CSV"/"Export as HTML" write the stat summary to a file
        // chosen in a file chooser (Swing KeYFileChooser with the statistics filter, :392-409);
        // "Save proof"/"Save proof bundle"/"Show Soundiness Report" stay out (the FX File/Save
        // and View/Soundiness entries cover them)
        Button csvButton = new Button("Export as CSV");
        csvButton.setOnAction(e -> export(owner, proof, "csv", getCSVStatisticsMessage(proof)));
        Button htmlButton = new Button("Export as HTML");
        htmlButton.setOnAction(e -> export(owner, proof, "html", getHTMLStatisticsMessage(proof)));
        HBox buttons = new HBox(8, csvButton, htmlButton, close);
        buttons.setAlignment(Pos.CENTER_RIGHT);
        VBox.setVgrow(buttons, Priority.NEVER);

        ScrollPane scroll = new ScrollPane(statsBox);
        scroll.setFitToWidth(true);
        scroll.setPrefViewportHeight(Math.min(240, 40 + 22 * statsBox.getChildren().size()));

        VBox root = new VBox(12, new Label("Proof " + proof.name()), scroll, buttons);
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

    /**
     * A4 (P3c): writes the CSV statistics message exactly like Swing
     * {@code ShowProofStatistics.getCSVStatisticsMessage} (ShowProofStatistics.java:86-121): the
     * open-goal line, the summary pairs separated by {@code ;}, and — when the proof has
     * interactive steps — the "interactive;rule;count" lines sorted by count (descending, then
     * rule name).
     *
     * @param proof the proof whose statistics to serialize
     * @return the CSV text
     */
    public static String getCSVStatisticsMessage(Proof proof) {
        final int openGoals = proof.openGoals().size();
        StringBuilder stats = new StringBuilder();
        stats.append("open goals" + CSV_SEPARATOR).append(openGoals).append("\n");

        final Statistics s = proof.getStatistics();

        for (Pair<String, String> x : s.getSummary()) {
            if ("".equals(x.second)) {
                stats.append(x.first).append("\n");
            } else {
                stats.append(x.first).append(CSV_SEPARATOR).append(x.second).append("\n");
            }
        }

        if (s.interactiveSteps > 0) {
            SortedSet<Map.Entry<String, Integer>> sortedEntries =
                new TreeSet<>(
                    (o1, o2) -> {
                        int cmpRes = o2.getValue().compareTo(o1.getValue());
                        if (cmpRes == 0) {
                            cmpRes = o1.getKey().compareTo(o2.getKey());
                        }
                        return cmpRes;
                    });
            sortedEntries.addAll(s.getInteractiveAppsDetails().entrySet());

            for (Map.Entry<String, Integer> entry : sortedEntries) {
                stats.append("interactive" + CSV_SEPARATOR).append(entry.getKey())
                        .append(CSV_SEPARATOR)
                        .append(entry.getValue()).append("\n");
            }
        }

        return stats.toString();
    }

    /**
     * A4 (P3c): the open-goal/cached-goal summary of the given node (Swing
     * {@code ShowProofStatistics.getHTMLStatisticsMessage(Node)},
     * ShowProofStatistics.java:123-139).
     *
     * @param node the node whose subtree statistics to summarize
     * @return the HTML statistics message
     */
    public static String getHTMLStatisticsMessage(Node node) {
        int openGoals = 0;
        int cachedGoals = 0;

        Iterator<Node> leavesIt = node.leavesIterator();
        while (leavesIt.hasNext()) {
            if (node.proof().getOpenGoal(leavesIt.next()) != null) {
                if (node.lookup(ClosedBy.class) != null) {
                    cachedGoals++;
                } else {
                    openGoals++;
                }
            }
        }

        return getHTMLStatisticsMessage(openGoals, cachedGoals, node.statistics());
    }

    /**
     * A4 (P3c): the open-goal/cached-goal summary of a proof (Swing
     * {@code ShowProofStatistics.getHTMLStatisticsMessage(Proof)},
     * ShowProofStatistics.java:141-147).
     *
     * @param proof the proof whose statistics to render
     * @return the HTML statistics message
     */
    public static String getHTMLStatisticsMessage(Proof proof) {
        int openGoals = proof.openGoals().size();
        int cachedGoals =
            (int) proof.closedGoals().stream().filter(g -> g.node().lookup(ClosedBy.class) != null)
                    .count();
        return getHTMLStatisticsMessage(openGoals, cachedGoals, proof.getStatistics());
    }

    private static String getHTMLStatisticsMessage(int openGoals, int cachedGoals,
            Statistics statistics) {
        StringBuilder stats = new StringBuilder("<html><head>" + "<style type=\"text/css\">"
            + "body {font-weight: normal; text-align: center;}" + "td {padding: 1px;}"
            + "th {padding: 2px; font-weight: bold;}" + "</style></head><body>");

        stats.append("<br>");
        if (cachedGoals > 0 && openGoals > 0) {
            stats.append("<strong>").append(openGoals).append(" open goal")
                    .append(openGoals > 1 ? "s, " : ", ").append(cachedGoals)
                    .append(" cached goal").append(cachedGoals > 1 ? "s." : ".")
                    .append("</strong>");
        } else if (cachedGoals > 0) {
            stats.append("<strong>").append("Proved (using proof cache).").append("</strong>");
        } else if (openGoals > 0) {
            stats.append("<strong>").append(openGoals).append(" open goal")
                    .append(openGoals > 1 ? "s." : ".").append("</strong>");
        } else {
            stats.append("<strong>Proved.</strong>");
        }

        stats.append("<br/><br/>");
        stats.append(getStatisticsTable(statistics));
        stats.append("</body></html>");
        return stats.toString();
    }

    private static String getStatisticsTable(Statistics s) {
        StringBuilder stats = new StringBuilder();
        stats.append("<table>");

        for (Pair<String, String> x : s.getSummary()) {
            if ("".equals(x.second)) {
                stats.append("<tr><th colspan=\"2\">").append(x.first).append("</th></tr>");
            } else {
                if (x.first.contains("[tooltip: ")) {
                    Matcher m = TOOLTIP_PATTERN.matcher(x.first);
                    if (m.find()) {
                        String tooltip = m.group(1);
                        stats.append("<tr><td class='tooltip' title='").append(tooltip)
                                .append("'>")
                                .append(x.first, 0, x.first.indexOf('['))
                                .append("</td><td>")
                                .append(x.second)
                                .append("</td></tr>");
                    } else {
                        stats.append("<tr><td>").append(x.first).append("</td><td>")
                                .append(x.second).append("</td></tr>");
                    }
                } else {
                    stats.append("<tr><td>").append(x.first).append("</td><td>").append(x.second)
                            .append("</td></tr>");
                }
            }
        }

        if (s.interactiveSteps > 0) {
            stats.append("<tr><th colspan=\"2\">" + "Details on Interactive Apps" + "</th></tr>");

            SortedSet<Map.Entry<String, Integer>> sortedEntries =
                new TreeSet<>(
                    (o1, o2) -> {
                        int cmpRes = o2.getValue().compareTo(o1.getValue());

                        if (cmpRes == 0) {
                            cmpRes = o1.getKey().compareTo(o2.getKey());
                        }

                        return cmpRes;
                    });
            sortedEntries.addAll(s.getInteractiveAppsDetails().entrySet());

            for (Map.Entry<String, Integer> entry : sortedEntries) {
                stats.append("<tr><td>").append(entry.getKey()).append("</td><td>")
                        .append(entry.getValue()).append("</td></tr>");
            }
        }

        stats.append("</table>");

        return stats.toString();
    }

    /**
     * A4 (P3c): writes the given statistics text to the chosen file (Swing
     * {@code ShowProofStatistics.Window.export}, ShowProofStatistics.java:392-409: a save file
     * chooser defaulting to {@code <valid proof name>.<extension>}, written as UTF-8). Success
     * and failure surface as toasts (the established FX info/error reporting).
     *
     * @param owner the owner window of the file chooser; may be {@code null}
     * @param proof the proof being exported (its name forms the default file name)
     * @param extension {@code "csv"} or {@code "html"}
     * @param text the statistics text to write
     */
    private static void export(Window owner, Proof proof, String extension, String text) {
        FileChooser chooser = new FileChooser();
        chooser.setTitle("Choose filename to save statistics");
        String descriptor = extension.equalsIgnoreCase("csv") ? "CSV" : "HTML";
        chooser.getExtensionFilters().add(new FileChooser.ExtensionFilter(
            descriptor + " statistics (*." + extension + ")", "*." + extension));
        chooser.setInitialFileName(
            MiscTools.toValidFileName(proof.name().toString()) + "." + extension);
        java.io.File file = owner == null ? chooser.showSaveDialog(null)
                : chooser.showSaveDialog(owner);
        if (file == null) {
            return;
        }
        try {
            writeExport(file.toPath(), text);
            NotificationManagerF.getInstance().notify(
                "Proof statistics exported to " + file.getAbsolutePath(), Kind.INFO);
        } catch (IOException e) {
            LOGGER.warn("Failed to write statistics export", e);
            NotificationManagerF.getInstance().notify(
                "Failed to export proof statistics: " + e.getMessage(), Kind.ERROR);
        }
    }

    /**
     * A4 (P3c): writes the statistics text to the given file as UTF-8 (the write step behind
     * {@link #export}; shared with the {@code key.fx.verify.uicontrol} self test so no file
     * chooser is needed there).
     *
     * @param file the target file
     * @param text the statistics text
     * @throws IOException if the file cannot be written
     */
    public static void writeExport(Path file, String text) throws IOException {
        try (BufferedWriter writer = Files.newBufferedWriter(file, StandardCharsets.UTF_8)) {
            writer.write(text);
        }
    }

    /**
     * A4 (P3c): self test of the statistics export behind the buttons — writes both the CSV and
     * the HTML format to files and asserts the Swing-parity content (the CSV row separator, the
     * HTML summary headline and table). Called by the {@code key.fx.verify.uicontrol} self test.
     *
     * @param proof the loaded demo proof to export, may be {@code null} (SKIP)
     * @return {@code "PASS ..."} / {@code "FAIL ..."} / {@code "SKIP (no proof)"}
     */
    public static String verifyStatisticsExport(Proof proof) {
        if (proof == null) {
            return "SKIP (no proof)";
        }
        Path dir;
        try {
            dir = Files.createTempDirectory("keyfx-statistics-export-");
        } catch (IOException e) {
            LOGGER.warn("Statistics export self test: cannot create temp dir", e);
            return "FAIL (no temp dir)";
        }
        try {
            Path csv = dir.resolve("stats.csv");
            Path html = dir.resolve("stats.html");
            writeExport(csv, getCSVStatisticsMessage(proof));
            writeExport(html, getHTMLStatisticsMessage(proof));
            String csvText = Files.readString(csv, StandardCharsets.UTF_8);
            String htmlText = Files.readString(html, StandardCharsets.UTF_8);
            boolean csvOk =
                csvText.lines().anyMatch(l -> l.startsWith("open goals" + CSV_SEPARATOR))
                        && csvText.contains(CSV_SEPARATOR);
            boolean htmlOk = htmlText.contains("open goal") && htmlText.contains("<table>")
                    && htmlText.startsWith("<html><head>");
            Files.deleteIfExists(csv);
            Files.deleteIfExists(html);
            Files.deleteIfExists(dir);
            return (csvOk && htmlOk)
                    ? "PASS (csv chars=" + csvText.length() + ", html chars=" + htmlText.length()
                        + ")"
                    : "FAIL (csvOk=" + csvOk + ", htmlOk=" + htmlOk + ")";
        } catch (IOException e) {
            LOGGER.warn("Statistics export self test failed", e);
            return "FAIL (" + e.getMessage() + ")";
        }
    }
}

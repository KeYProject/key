/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.actions;

import java.awt.*;
import java.awt.event.ActionEvent;
import java.awt.event.KeyAdapter;
import java.awt.event.KeyEvent;
import java.awt.event.MouseEvent;
import java.io.*;
import java.nio.charset.StandardCharsets;
import java.util.Iterator;
import java.util.Map;
import java.util.SortedSet;
import java.util.TreeSet;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import javax.swing.*;
import javax.swing.text.AttributeSet;
import javax.swing.text.html.HTML;
import javax.swing.text.html.HTMLDocument;

import de.uka.ilkd.key.gui.KeYFileChooser;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.configuration.Config;
import de.uka.ilkd.key.gui.fonticons.IconFactory;
import de.uka.ilkd.key.gui.notification.events.GeneralInformationEvent;
import de.uka.ilkd.key.gui.plugins.caching.DefaultReferenceSearchDialogListener;
import de.uka.ilkd.key.gui.plugins.caching.ReferenceSearchDialog;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.Statistics;
import de.uka.ilkd.key.proof.reference.ClosedBy;
import de.uka.ilkd.key.util.MiscTools;
import de.uka.ilkd.key.util.Pair;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

public class ShowProofStatistics extends MainWindowAction {
    private static final Logger LOGGER = LoggerFactory.getLogger(ShowProofStatistics.class);

    private static final long serialVersionUID = -8814798230037775905L;

    /**
     * Regex pattern to check for tooltips in statistics entries.
     */
    private static final Pattern TOOLTIP_PATTERN = Pattern.compile(".+\\[tooltip: (.+)]");

    /**
     * The proof to show statistics for. May be null if the currently selected proof
     * is to be shown.
     */
    private final Proof proof;

    public ShowProofStatistics(MainWindow mainWindow, Proof proof) {
        super(mainWindow);
        setName("Show Proof Statistics");
        setIcon(IconFactory.statistics(16));
        getMediator().enableWhenProofLoaded(this);

        this.proof = proof;
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        final Proof proof = this.proof == null ? getMediator().getSelectedProof() : this.proof;
        if (proof == null) {
            mainWindow.notify(new GeneralInformationEvent("No statistics available.",
                "If you wish to see the statistics " + "for a proof you have to load one first"));
        } else {
            Window win = new Window(mainWindow, proof);
            win.setVisible(true);
        }
    }

    /**
     * Gets the CSV statistics message.
     *
     * @param proof the proof
     * @return the CSV statistics message
     */
    public static String getCSVStatisticsMessage(Proof proof) {
        final int openGoals = proof.openGoals().size();
        StringBuilder stats = new StringBuilder();
        stats.append("open goals,").append(openGoals).append("\n");

        final Statistics s = proof.getStatistics();

        for (Pair<String, String> x : s.getSummary()) {
            if ("".equals(x.second)) {
                stats.append(x.first).append("\n");
            } else {
                stats.append(x.first).append(",").append(x.second).append("\n");
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
                stats.append("interactive,").append(entry.getKey()).append(",")
                        .append(entry.getValue()).append("\n");
            }
        }

        return stats.toString();
    }

    private static String getHTMLStatisticsMessage(Node node) {
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

    private static String getHTMLStatisticsMessage(Proof proof) {
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
        // sadly something like: .tooltip {text-decoration: underline dashed;}
        // is not possible, the underline is solid...

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
                    m.find();
                    String tooltip = m.group(1);
                    stats.append("<tr><td class='tooltip' title='").append(tooltip).append("'>")
                            .append(x.first, 0, x.first.indexOf('['))
                            .append("</td><td>")
                            .append(x.second)
                            .append("</td></tr>");
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
     * Shows proof statistics and allows the user to save them as HTML or CSV.
     *
     * @author lanzinger
     */
    public static final class Window extends JDialog {

        private static final long serialVersionUID = 1266280148508192284L;
        private final Proof proof;

        /**
         * Creates a new (initially invisible) proof statistics window.
         *
         * @param mainWindow the main windown.
         * @param proof the proof whose statistics to show.
         */
        public Window(MainWindow mainWindow, Proof proof) {
            super(mainWindow, "Proof Statistics");

            if (!EventQueue.isDispatchThread()) {
                throw new IllegalStateException("tried to open statistics dialog on worker thread");
            }

            this.proof = proof;

            String stats = ShowProofStatistics.getHTMLStatisticsMessage(proof);
            init(mainWindow, stats);
        }

        /**
         * Creates a new (initially invisible) proof statistics window.
         *
         * @param mainWindow the main windown.
         * @param node the node for which to show subtree statistics
         */
        public Window(MainWindow mainWindow, Node node) {
            super(mainWindow, "Proof Statistics");
            this.proof = node.proof();

            String stats = ShowProofStatistics.getHTMLStatisticsMessage(node);
            init(mainWindow, stats);
        }

        private void init(MainWindow mainWindow, String stats) {

            JEditorPane statisticsPane = new StatisticsEditorPane("text/html", stats);
            statisticsPane.setEditable(false);
            statisticsPane.setBorder(BorderFactory.createEmptyBorder());
            statisticsPane.setCaretPosition(0);
            statisticsPane.setBackground(MainWindow.getInstance().getBackground());

            JScrollPane scrollPane = new JScrollPane(statisticsPane);
            scrollPane.setBorder(BorderFactory.createEmptyBorder());

            Font myFont = UIManager.getFont(Config.KEY_FONT_PROOF_TREE);
            if (myFont != null) {
                statisticsPane.putClientProperty(JEditorPane.HONOR_DISPLAY_PROPERTIES,
                    Boolean.TRUE);
                statisticsPane.setFont(myFont);
            } else {
                LOGGER.debug("KEY_FONT_PROOF_TREE not available. Use standard font.");
            }

            JPanel buttonPane = new JPanel();
            JPanel buttonPane2 = new JPanel();

            JButton okButton = new JButton("Close");
            okButton.addActionListener(event -> dispose());

            JButton csvButton = new JButton("Export as CSV");
            csvButton.addActionListener(
                event -> export("csv", MiscTools.toValidFileName(proof.name().toString()),
                    ShowProofStatistics.getCSVStatisticsMessage(proof)));

            JButton htmlButton = new JButton("Export as HTML");
            htmlButton.addActionListener(
                event -> export("html", MiscTools.toValidFileName(proof.name().toString()),
                    ShowProofStatistics.getHTMLStatisticsMessage(proof)));

            JButton saveButton = new JButton("Save proof");
            saveButton.addActionListener(
                e -> mainWindow.getUserInterface().saveProof(proof, ".proof"));
            JButton saveBundleButton = new JButton("Save proof bundle");
            saveBundleButton
                    .addActionListener(e -> mainWindow.getUserInterface().saveProofBundle(proof));

            buttonPane.add(okButton);
            buttonPane.add(csvButton);
            buttonPane.add(htmlButton);
            buttonPane2.add(saveButton);
            buttonPane2.add(saveBundleButton);

            if (proof.closedGoals().stream()
                    .anyMatch(g -> g.node().lookup(ClosedBy.class) != null)) {
                JButton copyReferences = new JButton("Realize cached branches");
                copyReferences.setToolTipText("For each goal closed using the proof cache, copy " +
                    "the referenced proof steps into this proof.");
                copyReferences.addActionListener(e -> {
                    dispose();
                    ReferenceSearchDialog dialog =
                        new ReferenceSearchDialog(proof, new DefaultReferenceSearchDialogListener(
                            MainWindow.getInstance().getMediator()));
                    // show the dialog and start the copy
                    // (two callbacks because setVisible will block)
                    SwingUtilities.invokeLater(() -> dialog.setVisible(true));
                    SwingUtilities.invokeLater(dialog::apply);
                });
                buttonPane2.add(copyReferences);
            }

            getRootPane().setDefaultButton(okButton);
            getRootPane().addKeyListener(new KeyAdapter() {

                @Override
                public void keyTyped(KeyEvent e) {
                    if (e.getKeyCode() == KeyEvent.VK_ENTER) {
                        getRootPane().getDefaultButton().doClick();
                    }
                }
            });

            setLayout(new BorderLayout());
            add(scrollPane, BorderLayout.CENTER);
            JPanel buttonsPane = new JPanel();
            BoxLayout layout = new BoxLayout(buttonsPane, BoxLayout.Y_AXIS);
            buttonsPane.setLayout(layout);
            buttonsPane.add(Box.createVerticalGlue());
            buttonsPane.add(buttonPane);
            buttonsPane.add(buttonPane2);
            add(buttonsPane, BorderLayout.PAGE_END);

            pack();
            int w = Math.min(600, 50 + Math.max(scrollPane.getPreferredSize().width,
                buttonsPane.getPreferredSize().width));
            int h = Math.min(850,
                50 + scrollPane.getPreferredSize().height + buttonsPane.getPreferredSize().height);

            setSize(w, h);
            setLocationRelativeTo(mainWindow);
        }

        @Override
        public void setVisible(boolean visible) {
            super.setVisible(visible);
            if (visible) {
                requestFocus();
            }
        }

        private void export(String fileExtension, String fileName, String text) {
            KeYFileChooser fileChooser =
                KeYFileChooser.getFileChooser("Choose filename to save statistics");
            fileChooser.setFileFilter(KeYFileChooser.STATISTICS_FILTER);
            fileChooser.setSelectedFile(new File(fileName + "." + fileExtension));
            int result = fileChooser.showSaveDialog(this);
            if (result == JFileChooser.APPROVE_OPTION) {
                File file = fileChooser.getSelectedFile();
                try (BufferedWriter writer =
                    new BufferedWriter(new OutputStreamWriter(new FileOutputStream(file),
                        StandardCharsets.UTF_8))) {
                    writer.write(text);
                } catch (IOException e) {
                    LOGGER.warn("Failed to write", e);
                    assert false;
                }
            }
        }
    }

    /**
     * Document pane extended to show tooltips for labeled elements.
     *
     * @author Arne Keller
     */
    private static final class StatisticsEditorPane extends JEditorPane {
        public StatisticsEditorPane(String type, String text) {
            super(type, text);
            ToolTipManager.sharedInstance().registerComponent(this);
        }

        @Override
        public String getToolTipText(MouseEvent evt) {
            int pos = viewToModel2D(evt.getPoint());
            if (pos >= 0) {
                HTMLDocument hdoc = (HTMLDocument) getDocument();
                javax.swing.text.Element e = hdoc.getCharacterElement(pos);
                AttributeSet a = e.getAttributes();

                return (String) a.getAttribute(HTML.Attribute.TITLE);
            }
            return null;
        }
    }

}

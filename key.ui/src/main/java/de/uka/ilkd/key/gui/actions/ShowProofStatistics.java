package de.uka.ilkd.key.gui.actions;

import java.awt.BorderLayout;
import java.awt.Dimension;
import java.awt.Font;
import java.awt.event.ActionEvent;
import java.awt.event.KeyAdapter;
import java.awt.event.KeyEvent;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.util.Comparator;
import java.util.Map;
import java.util.Map.Entry;
import java.util.SortedSet;
import java.util.TreeSet;

import javax.swing.*;

import de.uka.ilkd.key.gui.KeYFileChooser;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.configuration.Config;
import de.uka.ilkd.key.gui.fonticons.IconFactory;
import de.uka.ilkd.key.gui.notification.events.GeneralInformationEvent;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.Statistics;
import de.uka.ilkd.key.proof.io.consistency.DiskFileRepo;
import de.uka.ilkd.key.util.Debug;
import de.uka.ilkd.key.util.MiscTools;
import de.uka.ilkd.key.util.Pair;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

public class ShowProofStatistics extends MainWindowAction {
    private static final Logger LOGGER = LoggerFactory.getLogger(ShowProofStatistics.class);

    /**
     *
     */
    private static final long serialVersionUID = -8814798230037775905L;

    public ShowProofStatistics(MainWindow mainWindow) {
        super(mainWindow);
        setName("Show Proof Statistics");
        setIcon(IconFactory.statistics(16));
        getMediator().enableWhenProofLoaded(this);
        lookupAcceleratorKey();
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        final Proof proof = getMediator().getSelectedProof();
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
        String stats = "";
        stats += "open goals," + openGoals + "\n";

        final Statistics s = proof.getStatistics();

        for (Pair<String, String> x : s.getSummary()) {
            if ("".equals(x.second)) {
                stats += x.first + "\n";
            } else {
                stats += x.first + "," + x.second + "\n";
            }
        }

        if (s.interactiveSteps > 0) {
            SortedSet<Map.Entry<String, Integer>> sortedEntries =
                new TreeSet<Map.Entry<String, Integer>>(
                    new Comparator<Map.Entry<String, Integer>>() {
                        @Override
                        public int compare(Entry<String, Integer> o1, Entry<String, Integer> o2) {
                            int cmpRes = o2.getValue().compareTo(o1.getValue());
                            if (cmpRes == 0) {
                                cmpRes = o1.getKey().compareTo(o2.getKey());
                            }
                            return cmpRes;
                        }
                    });
            sortedEntries.addAll(s.getInteractiveAppsDetails().entrySet());

            for (Map.Entry<String, Integer> entry : sortedEntries) {
                stats += "interactive," + entry.getKey() + "," + entry.getValue() + "\n";
            }
        }

        return stats;
    }

    public static String getHTMLStatisticsMessage(Proof proof) {
        final int openGoals = proof.openGoals().size();
        String stats = "<html><head>" + "<style type=\"text/css\">"
            + "body {font-weight: normal; text-align: center;}" + "td {padding: 1px;}"
            + "th {padding: 2px; font-weight: bold;}" + "</style></head><body>";

        if (openGoals > 0) {
            stats +=
                "<strong>" + openGoals + " open goal" + (openGoals > 1 ? "s." : ".") + "</strong>";
        } else {
            stats += "<strong>Proved.</strong>";
        }

        stats += "<br/><br/><table>";

        final Statistics s = proof.getStatistics();

        for (Pair<String, String> x : s.getSummary()) {
            if ("".equals(x.second)) {
                stats += "<tr><th colspan=\"2\">" + x.first + "</th></tr>";
            } else {
                stats += "<tr><td>" + x.first + "</td><td>" + x.second + "</td></tr>";
            }
        }

        if (s.interactiveSteps > 0) {
            stats += "<tr><th colspan=\"2\">" + "Details on Interactive Apps" + "</th></tr>";

            SortedSet<Map.Entry<String, Integer>> sortedEntries =
                new TreeSet<Map.Entry<String, Integer>>(
                    new Comparator<Map.Entry<String, Integer>>() {
                        @Override
                        public int compare(Entry<String, Integer> o1, Entry<String, Integer> o2) {
                            int cmpRes = o2.getValue().compareTo(o1.getValue());

                            if (cmpRes == 0) {
                                cmpRes = o1.getKey().compareTo(o2.getKey());
                            }

                            return cmpRes;
                        }
                    });
            sortedEntries.addAll(s.getInteractiveAppsDetails().entrySet());

            for (Map.Entry<String, Integer> entry : sortedEntries) {
                stats +=
                    "<tr><td>" + entry.getKey() + "</td><td>" + entry.getValue() + "</td></tr>";
            }
        }

        stats += "</table></body></html>";

        return stats;
    }

    /**
     * Shows proof statistics and allows the user to save them as HTML or CSV.
     *
     * @author lanzinger
     */
    public static final class Window extends JDialog {

        private static final long serialVersionUID = 1266280148508192284L;

        /**
         * Creates a new (initially invisible) proof statistics window.
         *
         * @param mainWindow the main windown.
         * @param proof the proof whose statistics to show.
         */
        public Window(MainWindow mainWindow, Proof proof) {
            super(mainWindow, "Proof Statistics");

            String stats = ShowProofStatistics.getHTMLStatisticsMessage(proof);

            JEditorPane statisticsPane = new JEditorPane("text/html", stats);
            statisticsPane.setEditable(false);
            statisticsPane.setBorder(BorderFactory.createEmptyBorder());
            statisticsPane.setCaretPosition(0);
            statisticsPane.setBackground(MainWindow.getInstance().getBackground());
            statisticsPane.setSize(new Dimension(10, 360));
            statisticsPane.setPreferredSize(
                new Dimension(statisticsPane.getPreferredSize().width + 15, 360));

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

            JButton okButton = new JButton("Close");
            okButton.addActionListener(event -> {
                dispose();
            });

            JButton csvButton = new JButton("Export as CSV");
            csvButton.addActionListener(event -> {
                export("csv", MiscTools.toValidFileName(proof.name().toString()),
                    ShowProofStatistics.getCSVStatisticsMessage(proof));
            });

            JButton htmlButton = new JButton("Export as HTML");
            htmlButton.addActionListener(event -> {
                export("html", MiscTools.toValidFileName(proof.name().toString()),
                    ShowProofStatistics.getHTMLStatisticsMessage(proof));
            });

            buttonPane.add(okButton);
            buttonPane.add(csvButton);
            buttonPane.add(htmlButton);

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
            add(buttonPane, BorderLayout.PAGE_END);

            int w = 50 + Math.max(scrollPane.getPreferredSize().width,
                buttonPane.getPreferredSize().width);
            int h =
                scrollPane.getPreferredSize().height + buttonPane.getPreferredSize().height + 100;
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
                    new BufferedWriter(new OutputStreamWriter(new FileOutputStream(file)));) {
                    writer.write(text);
                } catch (IOException e) {
                    e.printStackTrace();
                    assert false;
                }
            }
        }
    }

}

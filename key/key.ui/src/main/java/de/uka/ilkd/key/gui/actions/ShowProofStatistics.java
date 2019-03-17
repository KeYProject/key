// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.gui.actions;

import java.awt.Dimension;
import java.awt.Font;
import java.awt.event.ActionEvent;
import java.util.Comparator;
import java.util.Map;
import java.util.Map.Entry;
import java.util.SortedSet;
import java.util.TreeSet;

import javax.swing.BorderFactory;
import javax.swing.JEditorPane;
import javax.swing.JOptionPane;
import javax.swing.JScrollPane;
import javax.swing.UIManager;

import de.uka.ilkd.key.gui.IconFactory;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.configuration.Config;
import de.uka.ilkd.key.gui.notification.events.GeneralInformationEvent;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.Statistics;
import de.uka.ilkd.key.util.Debug;
import de.uka.ilkd.key.util.Pair;

public class ShowProofStatistics extends MainWindowAction {

    /**
     * 
     */
    private static final long serialVersionUID = -8814798230037775905L;

    public ShowProofStatistics(MainWindow mainWindow) {
        super(mainWindow);
        setName("Show Proof Statistics");
        setIcon(IconFactory.statistics(16));
        getMediator().enableWhenProofLoaded(this);
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        final Proof proof = getMediator().getSelectedProof();
        if (proof == null) {
            mainWindow.notify(new GeneralInformationEvent(
                    "No statistics available.",
                    "If you wish to see the statistics "
                            + "for a proof you have to load one first"));
        }
        else {
            String stats = getHTMLStatisticsMessage(proof);

            JEditorPane contentPane = new JEditorPane("text/html", stats);
            contentPane.setEditable(false);
            contentPane.setBorder(BorderFactory.createEmptyBorder());
            contentPane.setCaretPosition(0);
            contentPane.setBackground(MainWindow.getInstance().getBackground());
            contentPane.setSize(new Dimension(10, 360));
            contentPane.setPreferredSize(new Dimension(contentPane.getPreferredSize().width + 15, 360));
            
            JScrollPane scrollPane = new JScrollPane(contentPane);
            scrollPane.setBorder(BorderFactory.createEmptyBorder());
            
            Font myFont = UIManager.getFont(Config.KEY_FONT_PROOF_TREE);
            if (myFont != null) {
                contentPane.putClientProperty(JEditorPane.HONOR_DISPLAY_PROPERTIES, Boolean.TRUE);
                contentPane.setFont(myFont);
            } else {
                Debug.out("KEY_FONT_PROOF_TREE not available. Use standard font.");
            }
            
            JOptionPane.showMessageDialog(mainWindow, scrollPane,
                    "Proof Statistics", JOptionPane.INFORMATION_MESSAGE);
        }
    }

    public static String getHTMLStatisticsMessage(Proof proof) {
        final int openGoals = proof.openGoals().size();
        String stats = "<html><head>"
                + "<style type=\"text/css\">"
                + "body {font-weight: normal;}"
                + "td {padding: 1px;}"
                + "th {padding: 2px; font-weight: bold;}"
                + "</style></head><body>";

        if (openGoals > 0) {
            stats +=
                    "<strong>" + openGoals + " open goal"
                            + (openGoals > 1 ? "s." : ".") + "</strong>";
        }
        else {
            stats += "<strong>Proved.</strong>";
        }

        stats += "<br/><br/><table>";

        final Statistics s = proof.getStatistics();

        for (Pair<String, String> x : s.getSummary()) {
            if ("".equals(x.second)) {
                stats +=
                        "<tr><th colspan=\"2\">" + x.first
                                + "</th></tr>";
            }
            else {
                stats +=
                        "<tr><td>" + x.first + "</td><td>" + x.second
                                + "</td></tr>";
            }
        }

        if (s.interactiveSteps > 0) {
            stats +=
                    "<tr><th colspan=\"2\">"
                            + "Details on Interactive Apps"
                            + "</th></tr>";

            SortedSet<Map.Entry<String, Integer>> sortedEntries =
                    new TreeSet<Map.Entry<String, Integer>>(
                            new Comparator<Map.Entry<String, Integer>>() {
                                @Override
                                public int compare(
                                        Entry<String, Integer> o1,
                                        Entry<String, Integer> o2) {
                                    int cmpRes =
                                            o2.getValue().compareTo(
                                                    o1.getValue());

                                    if (cmpRes == 0) {
                                        cmpRes =
                                                o1.getKey().compareTo(
                                                        o2.getKey());
                                    }

                                    return cmpRes;
                                }
                            });
            sortedEntries.addAll(s.getInteractiveAppsDetails().entrySet());

            for (Map.Entry<String, Integer> entry : sortedEntries) {
                stats +=
                        "<tr><td>" + entry.getKey() + "</td><td>"
                                + entry.getValue() + "</td></tr>";
            }
        }

        stats += "</table></body></html>";
        
        return stats;
    }
}
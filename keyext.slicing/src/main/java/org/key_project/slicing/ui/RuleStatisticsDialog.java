/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.slicing.ui;

import java.awt.*;
import java.awt.event.KeyAdapter;
import java.awt.event.KeyEvent;
import java.util.*;
import java.util.List;
import javax.swing.*;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.configuration.Config;

import org.key_project.slicing.RuleStatistics;
import org.key_project.slicing.RuleStatistics.RuleStatisticEntry;
import org.key_project.slicing.analysis.AnalysisResults;

/**
 * Dialog that displays the results of the dependency analysis algorithm.
 *
 * @author Arne Keller
 */
public class RuleStatisticsDialog extends JDialog {
    /**
     * The rule statistics displayed in this dialog.
     */
    private final transient RuleStatistics statistics;

    /**
     * Construct and show a new dialog based on the provided analysis results.
     *
     * @param window main window
     * @param results the results to show
     */
    public RuleStatisticsDialog(Window window, AnalysisResults results) {
        super(window, "Rule Statistics");

        this.statistics = results.ruleStatistics;

        createUI(window);

        setVisible(true);
    }

    /**
     * Initialize the UI of this dialog.
     *
     * @param window main window
     */
    private void createUI(Window window) {
        setLayout(new BorderLayout());

        JEditorPane statisticsPane = new JEditorPane("text/html", "");
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
        }

        JPanel buttonPane = constructButtonPanel(statisticsPane);

        add(scrollPane, BorderLayout.CENTER);
        add(buttonPane, BorderLayout.PAGE_END);

        int w = 50
                + Math.max(
                    scrollPane.getPreferredSize().width,
                    buttonPane.getPreferredSize().width);
        int h = scrollPane.getPreferredSize().height
                + buttonPane.getPreferredSize().height
                + 100;
        setSize(w, h);

        statisticsPane.setText(genTable(
            statistics.sortBy(
                Comparator.comparing(RuleStatisticEntry::numberOfApplications)
                        .reversed())));
        statisticsPane.setCaretPosition(0);
        setLocationRelativeTo(window);
    }

    /**
     * Construct the buttons panel. Should be added to the main panel after construction.
     *
     * @param statisticsPane text pane showing the statistics
     * @return the buttons panel
     */
    private JPanel constructButtonPanel(JEditorPane statisticsPane) {
        JPanel buttonPane = new JPanel();

        JButton okButton = new JButton("Close");
        okButton.addActionListener(event -> dispose());
        KeyStroke stroke = KeyStroke.getKeyStroke(KeyEvent.VK_ESCAPE, 0);
        rootPane.registerKeyboardAction(e -> dispose(), stroke, JComponent.WHEN_IN_FOCUSED_WINDOW);

        JButton sortButton1 = new JButton("Sort by name");
        sortButton1.addActionListener(event -> {
            statisticsPane.setText(genTable(
                statistics.sortBy(Comparator.comparing(RuleStatisticEntry::ruleName))));
            statisticsPane.setCaretPosition(0);
        });
        JButton sortButton2 = new JButton("Sort by total");
        sortButton2.addActionListener(event -> {
            statisticsPane.setText(genTable(
                statistics.sortBy(
                    Comparator.comparing(RuleStatisticEntry::numberOfApplications).reversed())));
            statisticsPane.setCaretPosition(0);
        });
        JButton sortButton3 = new JButton("Sort by useless");
        sortButton3.addActionListener(event -> {
            statisticsPane.setText(genTable(
                statistics.sortBy(Comparator
                        .comparing(RuleStatisticEntry::numberOfUselessApplications).reversed())));
            statisticsPane.setCaretPosition(0);
        });
        JButton sortButton4 = new JButton("Sort by initial useless");
        sortButton4.addActionListener(event -> {
            statisticsPane.setText(genTable(
                statistics.sortBy(
                    Comparator.comparing(RuleStatisticEntry::numberOfInitialUselessApplications)
                            .reversed())));
            statisticsPane.setCaretPosition(0);
        });

        buttonPane.add(sortButton1);
        buttonPane.add(sortButton2);
        buttonPane.add(sortButton3);
        buttonPane.add(sortButton4);
        buttonPane.add(okButton);

        getRootPane().setDefaultButton(okButton);
        getRootPane().addKeyListener(new KeyAdapter() {

            @Override
            public void keyTyped(KeyEvent e) {
                if (e.getKeyCode() == KeyEvent.VK_ENTER || e.getKeyCode() == KeyEvent.VK_ESCAPE) {
                    getRootPane().getDefaultButton().doClick();
                }
            }
        });
        return buttonPane;
    }

    /**
     * Generate the HTML table to display in this dialog.
     *
     * @param rules statistics on rule apps (see {@link RuleStatistics})
     * @return HTML
     */
    private String genTable(List<RuleStatisticEntry> rules) {
        List<String> columns = List.of("Rule name", "Total applications", "Useless applications",
            "Initial useless applications");

        List<Collection<String>> rows = new ArrayList<>();
        // summary row
        int uniqueRules = rules.size();
        int totalSteps = rules.stream().mapToInt(RuleStatisticEntry::numberOfApplications).sum();
        int uselessSteps =
            rules.stream().mapToInt(RuleStatisticEntry::numberOfUselessApplications).sum();
        int initialUseless =
            rules.stream().mapToInt(RuleStatisticEntry::numberOfInitialUselessApplications).sum();
        rows.add(List.of(String.format("(all %d rules)", uniqueRules), Integer.toString(totalSteps),
            Integer.toString(uselessSteps), Integer.toString(initialUseless)));
        // next summary row
        List<RuleStatisticEntry> rulesBranching =
            rules.stream().filter(it -> statistics.branches(it.ruleName())).toList();
        int uniqueRules2 = rulesBranching.size();
        totalSteps =
            rulesBranching.stream().mapToInt(RuleStatisticEntry::numberOfApplications).sum();
        uselessSteps =
            rulesBranching.stream().mapToInt(RuleStatisticEntry::numberOfUselessApplications).sum();
        initialUseless = rulesBranching.stream()
                .mapToInt(RuleStatisticEntry::numberOfInitialUselessApplications).sum();
        rows.add(List.of(String.format("(%d branching rules)", uniqueRules2),
            Integer.toString(totalSteps), Integer.toString(uselessSteps),
            Integer.toString(initialUseless)));
        rules.forEach(a -> {
            String name = a.ruleName();
            Integer all = a.numberOfApplications();
            Integer useless = a.numberOfUselessApplications();
            Integer iua = a.numberOfInitialUselessApplications();
            rows.add(List.of(name, all.toString(), useless.toString(), iua.toString()));
        });

        return HtmlFactory.generateTable(columns, new boolean[] { false, false, false, false },
            Optional.of(new String[] { null, "right", "right", "right" }), rows, null);
    }
}

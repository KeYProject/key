/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.slicing.ui;

import java.awt.*;
import java.awt.event.KeyAdapter;
import java.awt.event.KeyEvent;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Comparator;
import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;
import javax.swing.*;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.configuration.Config;
import de.uka.ilkd.key.util.Quadruple;

import org.key_project.slicing.RuleStatistics;
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
                Comparator.comparing((Quadruple<String, Integer, Integer, Integer> it) -> it.second)
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
                statistics.sortBy(Comparator.comparing(it -> it.first))));
            statisticsPane.setCaretPosition(0);
        });
        JButton sortButton2 = new JButton("Sort by total");
        sortButton2.addActionListener(event -> {
            statisticsPane.setText(genTable(
                statistics.sortBy(
                    Comparator
                            .comparing(
                                (Quadruple<String, Integer, Integer, Integer> it) -> it.second)
                            .reversed())));
            statisticsPane.setCaretPosition(0);
        });
        JButton sortButton3 = new JButton("Sort by useless");
        sortButton3.addActionListener(event -> {
            statisticsPane.setText(genTable(
                statistics.sortBy(
                    Comparator
                            .comparing(
                                (Quadruple<String, Integer, Integer, Integer> it) -> it.third)
                            .reversed())));
            statisticsPane.setCaretPosition(0);
        });
        JButton sortButton4 = new JButton("Sort by initial useless");
        sortButton4.addActionListener(event -> {
            statisticsPane.setText(genTable(
                statistics.sortBy(
                    Comparator
                            .comparing(
                                (Quadruple<String, Integer, Integer, Integer> it) -> it.fourth)
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
    private String genTable(List<Quadruple<String, Integer, Integer, Integer>> rules) {
        List<String> columns = List.of("Rule name", "Total applications", "Useless applications",
            "Initial useless applications");

        List<Collection<String>> rows = new ArrayList<>();
        // summary row
        int uniqueRules = rules.size();
        int totalSteps = rules.stream().mapToInt(it -> it.second).sum();
        int uselessSteps = rules.stream().mapToInt(it -> it.third).sum();
        int initialUseless = rules.stream().mapToInt(it -> it.fourth).sum();
        rows.add(List.of(String.format("(all %d rules)", uniqueRules), Integer.toString(totalSteps),
            Integer.toString(uselessSteps), Integer.toString(initialUseless)));
        // next summary row
        List<Quadruple<String, Integer, Integer, Integer>> rulesBranching =
            rules.stream().filter(it -> statistics.branches(it.first)).collect(Collectors.toList());
        int uniqueRules2 = rulesBranching.size();
        totalSteps = rulesBranching.stream().mapToInt(it -> it.second).sum();
        uselessSteps = rulesBranching.stream().mapToInt(it -> it.third).sum();
        initialUseless = rulesBranching.stream().mapToInt(it -> it.fourth).sum();
        rows.add(List.of(String.format("(%d branching rules)", uniqueRules2),
            Integer.toString(totalSteps), Integer.toString(uselessSteps),
            Integer.toString(initialUseless)));
        rules.forEach(a -> {
            String name = a.first;
            Integer all = a.second;
            Integer useless = a.third;
            Integer iua = a.fourth;
            rows.add(List.of(name, all.toString(), useless.toString(), iua.toString()));
        });

        return HtmlFactory.generateTable(columns, new boolean[] { false, false, false, false },
            Optional.of(new String[] { null, "right", "right", "right" }), rows, null);
    }
}

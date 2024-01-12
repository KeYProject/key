/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.slicing.ui;

import java.awt.*;
import java.io.File;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Comparator;
import java.util.Deque;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.function.Function;
import java.util.stream.Collectors;
import javax.swing.*;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.configuration.Config;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;

import org.key_project.slicing.analysis.AnalysisResults;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Dialog to monitor slicing progress.
 * Automatically analyzes and slices the currently selected proof by simulating user interactions.
 * Intermediate proof slices are discarded automatically.
 *
 * @author Arne Keller
 */
public class SliceToFixedPointDialog extends JDialog implements KeYSelectionListener {
    /**
     * Logger.
     */
    private static final Logger LOGGER = LoggerFactory.getLogger(SliceToFixedPointDialog.class);

    /**
     * Active KeY mediator.
     */
    private final KeYMediator mediator;
    /**
     * Close button of this dialog.
     */
    private final JButton closeButton;
    /**
     * Text panel showing slicing progress in tabular form.
     */
    private final JEditorPane logPane;
    /**
     * Function that provides the analysis results of the last loaded proof.
     */
    private final Function<Void, AnalysisResults> analyzeButton;
    /**
     * Function that slices the currently loaded proof.
     */
    private final Runnable sliceButton;

    /**
     * Current slicing worker.
     */
    private SliceToFixedPointWorker worker;

    /**
     * Table data to display. Contains statistics on sliced away rule applications.
     */
    private final Collection<Collection<String>> tableRows = new ArrayList<>();
    /**
     * Stores for all slices in total: rule name -> number of times sliced away.
     */
    private final Map<String, Integer> slicedAway = new HashMap<>();

    /**
     * Construct a new dialog.
     *
     * @param mediator KeY mediator
     * @param window main window
     * @param analyzeCallback function that provides analysis results on the last loaded proof
     * @param sliceButton function that slices the last loaded proof
     */
    public SliceToFixedPointDialog(KeYMediator mediator, Window window,
            Function<Void, AnalysisResults> analyzeCallback,
            Runnable sliceButton) {
        super(window, "Slice to fixed point");

        this.mediator = mediator;
        // add this dialog as a selection listener, so we are always notified of
        // newly loaded (= sliced) proofs
        mediator.addKeYSelectionListener(this);
        // wrap the analysis callback to gather statistics on useless rule application
        this.analyzeButton = wrapAnalysisCallback(analyzeCallback);
        this.sliceButton = sliceButton;

        logPane = new JEditorPane("text/html", "");
        logPane.setEditable(false);
        logPane.setBorder(BorderFactory.createEmptyBorder());
        logPane.setCaretPosition(0);
        logPane.setBackground(MainWindow.getInstance().getBackground());
        logPane.setSize(new Dimension(10, 360));
        logPane.setPreferredSize(
            new Dimension(logPane.getPreferredSize().width + 15, 360));

        JScrollPane scrollPane = new JScrollPane(logPane);
        scrollPane.setBorder(BorderFactory.createEmptyBorder());

        Font myFont = UIManager.getFont(Config.KEY_FONT_PROOF_TREE);
        if (myFont != null) {
            logPane.putClientProperty(JEditorPane.HONOR_DISPLAY_PROPERTIES,
                Boolean.TRUE);
            logPane.setFont(myFont);
        }

        JPanel buttonPane = new JPanel();

        closeButton = new JButton("Close");
        closeButton.addActionListener(event -> {
            mediator.removeKeYSelectionListener(this);
            dispose();
        });

        buttonPane.add(closeButton);

        getRootPane().setDefaultButton(closeButton);

        setLayout(new BorderLayout());
        add(scrollPane, BorderLayout.CENTER);
        add(buttonPane, BorderLayout.PAGE_END);

        this.updateTable();
        setMinimumSize(new Dimension(800, 600));
        setLocationRelativeTo(window);

        setVisible(true);
    }

    /**
     * Wrap the provided analyze callback such that results of the callback will first be recorded
     * in {@link #tableRows}.
     *
     * @param analyzeCallback callback to provide analysis results
     * @return function that provides analysis results
     */
    private Function<Void, AnalysisResults> wrapAnalysisCallback(
            Function<Void, AnalysisResults> analyzeCallback) {
        return x -> {
            AnalysisResults results = null;
            try {
                results = analyzeCallback.apply(null);
            } catch (Exception e) {
                LOGGER.error("failed to analyze proof", e);
            }
            if (results != null) {
                try {
                    // record useless rule applications in map
                    Deque<Node> queue = new ArrayDeque<>(List.of(results.proof.root()));
                    while (!queue.isEmpty()) {
                        Node node = queue.pop();
                        node.childrenIterator().forEachRemaining(queue::add);
                        if (node.getAppliedRuleApp() == null
                                || results.usefulSteps.contains(node)) {
                            continue;
                        }
                        String name = node.getAppliedRuleApp().rule().displayName();
                        if (node.childrenCount() > 1) {
                            name = name + "*";
                        }
                        slicedAway.compute(
                            name,
                            (k, v) -> v == null ? 1 : v + 1);
                    }
                    File filename = results.proof.getProofFile();
                    String label =
                        filename != null ? filename.getName() : results.proof.name().toString();
                    tableRows.add(List.of(
                        label,
                        String.valueOf(results.totalSteps),
                        String.valueOf(results.usefulStepsNr),
                        String.valueOf(results.proof.countBranches()),
                        String.valueOf(results.usefulBranchesNr)));
                    SwingUtilities.invokeLater(this::updateTable);
                } catch (Exception e) {
                    LOGGER.error("failed to record statistics ", e);
                }
            }
            return results;
        };
    }

    private void updateTable() {
        String html = HtmlFactory.generateTable(
            List.of("Filename", "Total steps", "Useful steps", "Total branches", "Useful branches"),
            new boolean[] { false, false, false, false, false },
            Optional.of(new String[] { null, "right", "right", "right", "right" }),
            tableRows,
            null);
        List<Collection<String>> data = slicedAway
                .entrySet().stream()
                // sort inferences rule sliced away most to the start
                .sorted(Comparator.comparing(x -> -x.getValue()))
                .map(x -> (Collection<String>) List.of(x.getKey(), x.getValue().toString()))
                .collect(Collectors.toList());
        String html2 = HtmlFactory.generateTable(
            List.of("Inference rule", "Times sliced away"),
            new boolean[] { false, false },
            Optional.of(new String[] { null, "right" }),
            data,
            null);
        logPane.setText(html + "<hr/>" + html2);
        logPane.setCaretPosition(0); // scroll to top
    }

    /**
     * Start analyzing and slicing the currently selected proof.
     *
     * @param proof the currently selected proof
     */
    void start(Proof proof) {
        worker = new SliceToFixedPointWorker(proof, null, analyzeButton, sliceButton, () -> {
        });
        worker.execute();
    }

    @Override
    public void selectedProofChanged(KeYSelectionEvent e) {
        if (e.getSource().getSelectedProof() != null
                && e.getSource().getSelectedProof().closed()) {
            if (e.getSource().getSelectedProof() == worker.getSlicedProof()) {
                return; // no need to slice this one again
            }
            // pass previously sliced proof to worker, so that it is disposed of later
            worker = new SliceToFixedPointWorker(e.getSource().getSelectedProof(),
                worker.getSlicedProof(), analyzeButton, sliceButton, () -> {
                });
            worker.execute();
        }
    }
}

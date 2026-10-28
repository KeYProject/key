/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.slicing.ui;

import java.awt.*;
import java.nio.file.Path;
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

import org.key_project.prover.rules.RuleApp;
import org.key_project.slicing.analysis.AnalysisResults;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Dialog to monitor slicing progress.
 * Automatically analyzes and slices the currently selected proof by simulating user interactions.
 * Intermediate proof slices are discarded automatically.
 *
 * @author Arne Keller
 */
@NullMarked
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
    private final Function<Void, @Nullable AnalysisResults> analyzeButton;
    /**
     * Function that slices the currently loaded proof.
     */
    private final Runnable sliceButton;

    /**
     * Current slicing worker.
     */
    private @Nullable SliceToFixedPointWorker worker;

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
     * <p>
     * The listener registrations and UI calls below operate on {@code this} while the receiver is
     * still under initialization (EISOP initialization check); safe here since the dialog is
     * completed before it becomes visible and the listener callbacks only run after the
     * constructor has completed, suppressed with scoped keys.
     *
     * @param mediator KeY mediator
     * @param window main window
     * @param analyzeCallback function that provides analysis results on the last loaded proof
     * @param sliceButton function that slices the last loaded proof
     */
    @SuppressWarnings({ "nullness:method.invocation.invalid",
        "nullness:argument.type.incompatible" })
    public SliceToFixedPointDialog(KeYMediator mediator, Window window,
            Function<Void, @Nullable AnalysisResults> analyzeCallback,
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
    private Function<Void, @Nullable AnalysisResults> wrapAnalysisCallback(
            Function<Void, @Nullable AnalysisResults> analyzeCallback) {
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
                    Node root = results.proof.root();
                    if (root == null) {
                        throw new NullPointerException(
                            "No root node of the proof to slice.");
                    }
                    Deque<Node> queue = new ArrayDeque<>(List.of(root));
                    while (!queue.isEmpty()) {
                        Node node = queue.pop();
                        node.childrenIterator().forEachRemaining(queue::add);
                        if (node.getAppliedRuleApp() == null
                                || results.usefulSteps.contains(node)) {
                            continue;
                        }
                        RuleApp ruleApp = node.getAppliedRuleApp();
                        if (ruleApp == null) {
                            throw new NullPointerException(
                                "No rule application for node " + node.serialNr() + ".");
                        }
                        String name = ruleApp.rule().displayName();
                        if (node.childrenCount() > 1) {
                            name = name + "*";
                        }
                        slicedAway.compute(
                            name,
                            (k, v) -> v == null ? 1 : v + 1);
                    }
                    Path filename = results.proof.getProofFile();
                    String label;
                    if (filename != null) {
                        Path fileName = filename.getFileName();
                        label = fileName != null ? fileName.toString()
                                : results.proof.name().toString();
                    } else {
                        label = results.proof.name().toString();
                    }
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
        SliceToFixedPointWorker newWorker =
            new SliceToFixedPointWorker(proof, null, analyzeButton, sliceButton, () -> {
            });
        worker = newWorker;
        newWorker.execute();
    }

    @Override
    public void selectedProofChanged(KeYSelectionEvent<Proof> e) {
        Proof selectedProof = e.getSource().getSelectedProof();
        if (selectedProof != null && selectedProof.closed()) {
            SliceToFixedPointWorker currentWorker = worker;
            if (currentWorker == null) {
                throw new NullPointerException("No active slicing worker.");
            }
            if (selectedProof == currentWorker.getSlicedProof()) {
                return; // no need to slice this one again
            }
            // pass previously sliced proof to worker, so that it is disposed of later
            SliceToFixedPointWorker newWorker = new SliceToFixedPointWorker(selectedProof,
                currentWorker.getSlicedProof(), analyzeButton, sliceButton, () -> {
                });
            worker = newWorker;
            newWorker.execute();
        }
    }
}

package org.key_project.slicing.ui;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.configuration.Config;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import org.key_project.slicing.AnalysisResults;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import javax.swing.*;
import java.awt.*;
import java.io.File;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Comparator;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.function.Function;
import java.util.stream.Collectors;

/**
 * Dialog to monitor slicing progress.
 * Automatically analyzes and slices the currently selected proof by simulating user interactions.
 * Intermediate proof slices are discarded automatically.
 *
 * @author Arne Keller
 */
public class SliceToFixedPointDialog extends JDialog implements KeYSelectionListener {
    private static final Logger LOGGER = LoggerFactory.getLogger(SliceToFixedPointDialog.class);

    private final KeYMediator mediator;
    private final JButton closeButton;
    private final JEditorPane logPane;
    private final Function<Void, AnalysisResults> analyzeButton;
    private final Runnable sliceButton;

    private boolean cancelled = false;
    private boolean done = false;
    private SliceToFixedPointWorker worker;

    /**
     * Table data to display. Contains statistics on sliced away rule applications.
     */
    private Collection<Collection<String>> tableRows = new ArrayList<>();
    /**
     * Stores for all slices in total: rule name -> number of times sliced away.
     */
    private Map<String, Integer> slicedAway = new HashMap<>();

    public SliceToFixedPointDialog(KeYMediator mediator, Window window,
            Function<Void, AnalysisResults> analyzeCallback,
            Runnable sliceButton) {
        super(window, "Slice to fixed point");

        this.mediator = mediator;
        mediator.addKeYSelectionListener(this);
        this.analyzeButton = x -> {
            AnalysisResults results = null;
            try {
                results = analyzeCallback.apply(null);
            } catch (Exception e) {
                LOGGER.error("failed to analyze proof", e);
                done();
            }
            if (results != null) {
                try {
                    // record useless rule applications in map
                    var queue = new ArrayDeque<>(List.of(results.proof.root()));
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
                        "" + results.totalSteps,
                        "" + results.usefulStepsNr,
                        "" + results.proof.countBranches(),
                        "" + results.usefulBranchesNr));
                    SwingUtilities.invokeLater(this::updateTable);
                } catch (Exception e) {
                    e.printStackTrace();
                }
            }
            if (cancelled) {
                done();
                return null;
            } else {
                return results;
            }
        };
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
        closeButton.setEnabled(false);
        closeButton.setToolTipText("Cancel slicer first.");
        closeButton.addActionListener(event -> dispose());
        JButton cancel = new JButton("Cancel");
        cancel.addActionListener(event -> {
            cancel.setEnabled(false);
            mediator.removeKeYSelectionListener(this);
            cancelled = true;
        });

        buttonPane.add(cancel);
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
        worker = new SliceToFixedPointWorker(proof, null, analyzeButton, sliceButton,
            this::done);
        worker.execute();
    }

    private void done() {
        done = true;
        SwingUtilities.invokeLater(() -> {
            closeButton.setEnabled(true);
            closeButton.setToolTipText(null);
        });
    }

    @Override
    public void selectedProofChanged(KeYSelectionEvent e) {
        if (cancelled) {
            SwingUtilities.invokeLater(() -> mediator.removeKeYSelectionListener(this));
            done();
            return;
        }
        if (done) {
            SwingUtilities.invokeLater(() -> mediator.removeKeYSelectionListener(this));
            return;
        }
        if (e.getSource().getSelectedProof() != null
                && e.getSource().getSelectedProof().closed()) {
            if (e.getSource().getSelectedProof() == worker.getSlicedProof()) {
                return; // no need to slice this one again
            }
            // pass previously sliced proof to worker, so that it is disposed of later
            worker = new SliceToFixedPointWorker(e.getSource().getSelectedProof(),
                worker.getSlicedProof(),
                analyzeButton, sliceButton, this::done);
            worker.execute();
        }
    }
}

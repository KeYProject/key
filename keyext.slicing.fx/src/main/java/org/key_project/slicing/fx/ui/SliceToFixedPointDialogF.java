/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.slicing.fx.ui;

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
import java.util.function.Supplier;
import java.util.stream.Collectors;
import javafx.geometry.Insets;
import javafx.scene.Scene;
import javafx.scene.control.Button;
import javafx.scene.control.ButtonBar;
import javafx.scene.layout.BorderPane;
import javafx.scene.web.WebView;

import de.uka.ilkd.key.core.fx.KeYMediatorF;
import de.uka.ilkd.key.core.fx.KeYSelectionEvent;
import de.uka.ilkd.key.core.fx.KeYSelectionListener;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;

import org.key_project.slicing.analysis.AnalysisResults;
import org.key_project.slicing.ui.HtmlFactory;
import org.key_project.util.javafx.FxUtil;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Dialog to monitor slicing progress, FX port of
 * {@code org.key_project.slicing.ui.SliceToFixedPointDialog}: automatically analyzes and slices
 * the currently selected proof until the fixed point is reached (no more steps can be removed),
 * simulating the user interactions just like the Swing original — each iteration runs the
 * analyze callback, and if more steps may be removed it triggers the slice callback (which
 * slices and loads the next proof through the direct loader, keeping it out of the recent-files
 * list). The dialog listens on the mediator's selection model to observe each newly loaded
 * (closed) slice and starts the next worker; intermediate proof slices are discarded
 * automatically.
 * <p>
 * The progress tables (per-iteration step counts and the "times sliced away" statistics) are
 * shown in the {@link HtmlDialogF} WebView seam using {@link HtmlFactory#generateTable}, like
 * the Swing dialog's {@code JEditorPane}.
 * <p>
 * Deviations from the Swing original: the FX dialog is a {@link javafx.stage.Stage} instead of
 * a modal {@code JDialog} (the panel has no modal dialog infrastructure); everything else
 * mirrors the Swing worker/selection-listener choreography.
 *
 * @author Alexander Weigl (FX port)
 * @author Arne Keller (Swing original)
 */
@NullMarked
public class SliceToFixedPointDialogF extends javafx.stage.Stage
        implements KeYSelectionListener {

    private static final Logger LOGGER = LoggerFactory.getLogger(SliceToFixedPointDialogF.class);

    /** Active KeY mediator. */
    private final KeYMediatorF mediator;
    /**
     * Function that provides the analysis results of the last loaded proof (wrapped to record
     * the statistics of this dialog).
     */
    private final Supplier<@Nullable AnalysisResults> analyzeCallback;
    /** Function that slices the currently loaded proof. */
    private final Runnable sliceCallback;

    /** Text pane showing slicing progress in tabular form (Swing {@code logPane}). */
    private final WebView logPane;

    /** Current slicing worker. */
    private @Nullable SliceToFixedPointWorkerF worker;

    /** Table data to display. Contains statistics on sliced away rule applications. */
    private final List<List<String>> tableRows = new ArrayList<>();
    /**
     * Stores for all slices in total: rule name -> number of times sliced away.
     */
    private final Map<String, Integer> slicedAway = new HashMap<>();

    /** Whether the fixed point was reached (the last analysis found nothing more to remove). */
    private boolean converged = false;
    /** Number of analyze/slice iterations started in this dialog. */
    private int iterationCount = 0;

    /**
     * Construct a new dialog (Swing {@code SliceToFixedPointDialog(KeYMediator, Window,
     * Function, Runnable)}): registers itself as a selection listener, so it is always notified
     * of newly loaded (= sliced) proofs.
     *
     * @param mediator KeY mediator
     * @param owner owner window, may be {@code null}
     * @param analyzeCallback function that provides analysis results on the last loaded proof
     * @param sliceCallback function that slices the last loaded proof
     */
    public SliceToFixedPointDialogF(KeYMediatorF mediator,
            javafx.stage.@Nullable Window owner,
            Supplier<@Nullable AnalysisResults> analyzeCallback, Runnable sliceCallback) {
        setTitle("Slice to fixed point");
        this.mediator = mediator;
        mediator.getSelectionModel().addKeYSelectionListener(this);
        // wrap the analysis callback to gather statistics on useless rule applications
        this.analyzeCallback = wrapAnalysisCallback(analyzeCallback);
        this.sliceCallback = sliceCallback;

        logPane = new WebView();
        logPane.setPrefSize(700, 400);
        updateTable();

        Button closeButton = new Button("Close");
        closeButton.setOnAction(e -> {
            mediator.getSelectionModel().removeKeYSelectionListener(this);
            close();
        });
        ButtonBar.setButtonData(closeButton, ButtonBar.ButtonData.OK_DONE);
        closeButton.setDefaultButton(true);
        ButtonBar buttonBar = new ButtonBar();
        buttonBar.getButtons().add(closeButton);
        BorderPane.setMargin(buttonBar, new Insets(10));

        BorderPane root = new BorderPane(logPane, null, null, buttonBar, null);
        setScene(new Scene(root, 760, 520));
        if (owner != null) {
            initOwner(owner);
        }
        show();
    }

    /**
     * Wrap the provided analyze callback such that results of the callback will first be
     * recorded in {@link #tableRows} (Swing {@code SliceToFixedPointDialog.wrapAnalysisCallback}).
     *
     * @param callback callback to provide analysis results
     * @return function that provides analysis results
     */
    private Supplier<@Nullable AnalysisResults> wrapAnalysisCallback(
            Supplier<@Nullable AnalysisResults> callback) {
        return () -> {
            @Nullable
            AnalysisResults results;
            try {
                results = callback.get();
            } catch (Exception e) {
                LOGGER.error("failed to analyze proof", e);
                results = null;
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
                        synchronized (this) {
                            slicedAway.compute(name, (k, v) -> v == null ? 1 : v + 1);
                        }
                    }
                    Path filename = results.proof.getProofFile();
                    String label = filename != null
                            ? filename.getFileName().toString()
                            : results.proof.name().toString();
                    synchronized (this) {
                        tableRows.add(List.of(
                            label,
                            String.valueOf(results.totalSteps),
                            String.valueOf(results.usefulStepsNr),
                            String.valueOf(results.proof.countBranches()),
                            String.valueOf(results.usefulBranchesNr)));
                    }
                    FxUtil.runLater(this::updateTable);
                } catch (Exception e) {
                    LOGGER.error("failed to record statistics ", e);
                }
            }
            return results;
        };
    }

    /** Re-render the progress tables (Swing {@code SliceToFixedPointDialog.updateTable}). */
    private void updateTable() {
        List<Collection<String>> rows;
        Map<String, Integer> away;
        synchronized (this) {
            rows = List.copyOf(tableRows);
            away = Map.copyOf(slicedAway);
        }
        String html = HtmlFactory.generateTable(
            List.of("Filename", "Total steps", "Useful steps", "Total branches",
                "Useful branches"),
            new boolean[] { false, false, false, false, false },
            Optional.of(new String[] { null, "right", "right", "right", "right" }),
            rows,
            null);
        List<Collection<String>> data = away.entrySet().stream()
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
        logPane.getEngine().loadContent(html + "<hr/>" + html2, "text/html");
    }

    /**
     * Start analyzing and slicing the currently selected proof (Swing
     * {@code SliceToFixedPointDialog.start}).
     *
     * @param proof the currently selected proof
     */
    public void start(Proof proof) {
        worker = newWorker(proof, null);
        worker.execute();
    }

    /** Builds and registers a new worker (Swing worker construction in the listener). */
    private SliceToFixedPointWorkerF newWorker(Proof proof, @Nullable Proof proofToDispose) {
        iterationCount++;
        return new SliceToFixedPointWorkerF(proof, proofToDispose, analyzeCallback, sliceCallback,
            () -> {
                LOGGER.info("Slice to fixed point: converged after {} iteration(s)",
                    iterationCount);
                converged = true;
            });
    }

    @Override
    public void selectedProofChanged(KeYSelectionEvent<Proof> e) {
        FxUtil.runLater(() -> {
            Proof selected = e.getSource().getSelectedProof();
            if (selected == null || !selected.closed()) {
                return;
            }
            SliceToFixedPointWorkerF current = worker;
            if (current != null && selected == current.getSlicedProof()) {
                return; // no need to slice this one again
            }
            // pass previously sliced proof to worker, so that it is disposed of later
            worker = newWorker(selected, current != null ? current.getSlicedProof() : null);
            worker.execute();
        });
    }

    @Override
    public void selectedNodeChanged(KeYSelectionEvent<de.uka.ilkd.key.proof.Node> e) {
        // the dialog only reacts to proof switches
    }

    /** @return whether the fixed point was reached (verify harness seam) */
    public boolean isConverged() {
        return converged;
    }

    /** @return the number of analyze/slice iterations started (verify harness seam) */
    public int iterationCount() {
        return iterationCount;
    }

    /** @return the web view showing the progress tables (verify harness seam) */
    public WebView getWebView() {
        return logPane;
    }
}

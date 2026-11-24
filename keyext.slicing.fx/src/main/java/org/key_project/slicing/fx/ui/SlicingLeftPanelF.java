/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.slicing.fx.ui;

import java.io.BufferedWriter;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Collection;
import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;
import javafx.application.Platform;
import javafx.concurrent.Task;
import javafx.geometry.Insets;
import javafx.scene.Node;
import javafx.scene.control.Alert;
import javafx.scene.control.Button;
import javafx.scene.control.CheckBox;
import javafx.scene.control.Label;
import javafx.scene.control.ScrollPane;
import javafx.scene.control.TextArea;
import javafx.scene.control.TitledPane;
import javafx.scene.layout.Priority;
import javafx.scene.layout.VBox;
import javafx.scene.web.WebView;
import javafx.stage.FileChooser;

import de.uka.ilkd.key.core.fx.KeYMediatorF;
import de.uka.ilkd.key.core.fx.KeYSelectionEvent;
import de.uka.ilkd.key.core.fx.KeYSelectionListener;
import de.uka.ilkd.key.gui.fx.MainWindowF;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofTreeEvent;
import de.uka.ilkd.key.proof.ProofTreeListener;
import de.uka.ilkd.key.proof.io.ProblemLoaderControl;
import de.uka.ilkd.key.settings.GeneralSettings;
import de.uka.ilkd.key.settings.ProofIndependentSettings;

import org.key_project.slicing.DependencyTracker;
import org.key_project.slicing.SlicingProofReplayer;
import org.key_project.slicing.SlicingSettingsProvider;
import org.key_project.slicing.analysis.AnalysisResults;
import org.key_project.slicing.fx.SlicingExtensionF;
import org.key_project.slicing.ui.HtmlFactory;
import org.key_project.util.javafx.FxUtil;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * The proof-slicing left panel, FX port of {@code org.key_project.slicing.ui.SlicingLeftPanel}
 * (Swing SlicingLeftPanel.java): the dependency-graph stats and export controls, the proof
 * analysis controls and the slicing buttons, rendered with pure JavaFX controls. The underlying
 * logic (dependency tracking, analysis, slicing) is reused from {@code keyext.slicing} unchanged.
 * <p>
 * Parity notes (compared to the Swing panel): "Show rendering of graph" renders the DOT through
 * the graphviz {@code dot} binary and shows the image in the {@link PreviewDialogF} (with the
 * DOT-source text dialog as the documented fallback when rendering fails); "Slice proof to fixed
 * point" opens the iterative {@link SliceToFixedPointDialogF}; "Show rule statistics" renders
 * the HTML table with the four sort buttons of the Swing original in the {@link HtmlDialogF}
 * WebView seam; the execution timings are shown as an {@link HtmlFactory} HTML table like in the
 * Swing panel. Remaining, deliberate simplifications:
 * <ul>
 * <li>the 100 ms update debounce of the graph labels is dropped ({@link FxUtil}-marshalled
 * direct updates);</li>
 * <li>the "Export as DOT" file chooser runs owner-less (the drawer panel has no dedicated
 * window);</li>
 * <li>the slice load uses the FX window's own user-interface control instead of the Swing
 * headless {@code DefaultUserInterfaceControl} (both are {@code ProblemLoaderControl}s), so the
 * loader callbacks stay FX-safe;</li>
 * <li>the panel grey-out checks the parallel-prover setting directly instead of the Swing-only
 * {@code SingleCoreFeatureGate}.</li>
 * </ul>
 *
 * @author Alexander Weigl
 * @author Arne Keller (port)
 */
@NullMarked
public class SlicingLeftPanelF extends ScrollPane
        implements KeYSelectionListener, ProofTreeListener {

    private static final Logger LOGGER = LoggerFactory.getLogger(SlicingLeftPanelF.class);

    private static final String NO_PROOF_SELECTED = "No proof selected";

    /** KeY mediator instance. */
    private final KeYMediatorF mediator;
    /** Extension instance. */
    private final SlicingExtensionF extension;

    /** The proof currently shown in the KeY UI. */
    private @Nullable Proof currentProof = null;

    /** "Export as DOT" button. */
    private Button dotExport = null;
    /** "Show rendering of graph" button. */
    private Button showGraphRendering = null;
    /** "Slice proof" button. */
    private Button sliceProof = null;
    /** "Slice proof to fixed point" button. */
    private Button sliceProofFixedPoint = null;
    /** "Run analysis" button. */
    private Button runAnalysis = null;
    /** "Show rule statistics" button. */
    private Button showRuleStatistics = null;
    /** Label indicating the number of dependency graph nodes. */
    private Label graphNodes = null;
    /** Label indicating the number of dependency graph edges. */
    private Label graphEdges = null;
    /** Label showing total number of steps in the analyzed proof. */
    private Label totalSteps = null;
    /** Label showing number of useful steps as determined by the analysis. */
    private Label usefulSteps = null;
    /** Label showing total number of branches in the analyzed proof. */
    private Label totalBranches = null;
    /** Label showing number of useful branches as determined by the analysis. */
    private Label usefulBranches = null;
    /** Checkbox to abbreviate formulas in DOT output. */
    private CheckBox abbreviateFormulas = null;
    /** Checkbox to shorten chains in DOT output. */
    private CheckBox abbreviateChains = null;
    /** Checkbox to enable the dependency analysis algorithm. */
    private CheckBox doDependencyAnalysis = null;
    /** Checkbox to enable rule de-duplication. */
    private CheckBox doDeduplicateRuleApps = null;
    /** Panel showing the execution time of the algorithms. */
    private VBox timings = null;
    /** Titled section wrapping {@link #timings}, hidden until an analysis ran. */
    private TitledPane timingsPane = null;
    /**
     * The WebView rendering the {@link HtmlFactory} timings table (lazily created, reused across
     * analyses to avoid spawning a WebKit instance per update).
     */
    private @Nullable WebView timingsView = null;
    /** Whether the graphviz dot executable is available (checked once at panel build). */
    private final boolean dotAvailable = GraphvizDotExecutorF.isDotInstalled();

    /** Number of nodes in the dependency graph. */
    private int graphNodesNr = 0;
    /** Number of edges in the dependency graph. */
    private int graphEdgesNr = 0;

    /**
     * Construct a new panel for this extension (Swing SlicingLeftPanel constructor).
     *
     * @param mediator the KeY mediator
     * @param extension instance of the extension
     */
    public SlicingLeftPanelF(KeYMediatorF mediator, SlicingExtensionF extension) {
        super();
        this.mediator = mediator;
        this.extension = extension;

        buildUI();

        updateUIState();

        // Keep the slice buttons in sync with the prover mode (slicing is single-core only).
        // The property-change listener may fire from the prover thread, so marshal the UI
        // refresh onto the FX thread.
        ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings().addPropertyChangeListener(
            GeneralSettings.PARALLEL_PROVER_ENABLED,
            evt -> org.key_project.util.javafx.FxUtil.runLater(this::updateUIState));
    }

    /** Build the JavaFX control tree (Swing {@code SlicingLeftPanel.buildUI}). */
    private void buildUI() {
        VBox content = new VBox(10);
        content.setPadding(new Insets(10));
        content.getChildren().addAll(getDependencyGraphPanel(), getProofAnalysisPanel(),
            getProofSlicingPanel(), getTimingsPanel());
        setContent(content);
        setFitToWidth(true);
        setHbarPolicy(ScrollBarPolicy.NEVER);
    }

    /** The "Dependency graph" section (Swing {@code getDependencyGraphPanel}). */
    private TitledPane getDependencyGraphPanel() {
        abbreviateFormulas = new CheckBox("Abbreviate node labels");
        abbreviateFormulas.setTooltip(nativeTooltip("Replace node labels with their hash value."));
        abbreviateChains = new CheckBox("Shorten long chains");
        abbreviateChains.setTooltip(nativeTooltip("""
                Collapse long chains when rendering the graph.
                 When enabled: dependency graph nodes with both input and output degree equal to one
                 will be collapsed.
                 These shortened edges are labeled by: initial step ... last step"""));
        dotExport = new Button("Export as DOT");
        dotExport.setMaxWidth(Double.MAX_VALUE);
        dotExport.setOnAction(e -> exportDot());
        showGraphRendering = new Button("Show rendering of graph");
        showGraphRendering.setMaxWidth(Double.MAX_VALUE);
        showGraphRendering.setOnAction(e -> previewGraph());
        if (!dotAvailable) {
            // Swing SlicingLeftPanel.buildUI: graph rendering requires the graphviz dot binary
            showGraphRendering.setDisable(true);
            showGraphRendering.setTooltip(nativeTooltip(
                "Install graphviz (dot) to enable graph rendering functionality."));
        }

        graphNodes = new Label();
        graphEdges = new Label();
        resetGraphLabels();

        return titledPane("Dependency graph", List.of(graphNodes, graphEdges,
            abbreviateFormulas, abbreviateChains, dotExport, showGraphRendering));
    }

    /** The "Proof analysis" section (Swing {@code getProofAnalysisPanel}). */
    private TitledPane getProofAnalysisPanel() {
        totalSteps = new Label();
        usefulSteps = new Label();
        totalBranches = new Label();
        usefulBranches = new Label();
        doDependencyAnalysis = new CheckBox("Dependency analysis");
        doDependencyAnalysis.setSelected(true);
        doDependencyAnalysis.setOnAction(e -> resetLabels());
        doDeduplicateRuleApps = new CheckBox("De-duplicate rule applications");
        doDeduplicateRuleApps.setSelected(false);
        doDeduplicateRuleApps.setOnAction(e -> resetLabels());
        runAnalysis = new Button("Run analysis");
        runAnalysis.setMaxWidth(Double.MAX_VALUE);
        runAnalysis.setOnAction(e -> analyzeProof());
        showRuleStatistics = new Button("Show rule statistics");
        showRuleStatistics.setMaxWidth(Double.MAX_VALUE);
        showRuleStatistics.setOnAction(e -> showRuleStatistics());

        return titledPane("Proof analysis", List.of(totalSteps, usefulSteps, totalBranches,
            usefulBranches, doDependencyAnalysis, doDeduplicateRuleApps, runAnalysis,
            showRuleStatistics));
    }

    /** The "Proof slicing" section (Swing {@code buildUI} panel3). */
    private TitledPane getProofSlicingPanel() {
        sliceProof = new Button("Slice proof");
        sliceProof.setMaxWidth(Double.MAX_VALUE);
        sliceProof.setOnAction(e -> sliceProof());
        sliceProofFixedPoint = new Button("Slice proof to fixed point");
        sliceProofFixedPoint.setMaxWidth(Double.MAX_VALUE);
        sliceProofFixedPoint.setOnAction(e -> openSliceToFixedPointDialog());
        sliceProofFixedPoint.setTooltip(nativeTooltip(
            """
                    Slices the proof and analyzes the result; the process repeats until no more steps can
                    be removed."""));

        return titledPane("Proof slicing", List.of(sliceProof, sliceProofFixedPoint));
    }

    /** The (initially hidden) "Execution timings" section (Swing {@code timings}). */
    private TitledPane getTimingsPanel() {
        timings = new VBox(4);
        timingsPane = titledPane("Execution timings", List.of(timings));
        timingsPane.setVisible(false);
        return timingsPane;
    }

    /** Creates a titled section and the one-column vertical stack of its children. */
    private static TitledPane titledPane(String title, List<Node> children) {
        VBox box = new VBox(6);
        box.getChildren().addAll(children);
        TitledPane pane = new TitledPane(title, box);
        pane.setAnimated(false);
        return pane;
    }

    /** A plain JavaFX tooltip (the Swing original uses Swing HTML tooltips). */
    private static javafx.scene.control.Tooltip nativeTooltip(String text) {
        javafx.scene.control.Tooltip tooltip = new javafx.scene.control.Tooltip(text);
        tooltip.setWrapText(true);
        return tooltip;
    }

    /** Export the dependency graph as a DOT file (Swing {@code SlicingLeftPanel.exportDot}). */
    private void exportDot() {
        if (currentProof == null) {
            return;
        }
        DependencyTracker tracker = extension.trackers.get(currentProof);
        if (tracker == null) {
            return;
        }
        FileChooser fileChooser = new FileChooser();
        fileChooser.setTitle("Choose filename to save dot file");
        fileChooser.setInitialFileName("export.dot");
        // KNOWN-SIMPLIFIED: the Swing original passes the file-chooser parent component; the FX
        // chooser runs owner-less instead (the drawer panel has no dedicated window).
        java.io.File file = fileChooser.showSaveDialog(null);
        if (file == null) {
            return;
        }
        try (BufferedWriter writer = Files.newBufferedWriter(file.toPath(),
            StandardCharsets.UTF_8)) {
            writer.write(tracker.exportDot(abbreviateFormulas.isSelected(),
                abbreviateChains.isSelected()));
        } catch (IOException exc) {
            LOGGER.error("failed to export DOT file", exc);
            showError(exc);
        }
    }

    /** Show the rule statistics of the current proof (Swing {@code showRuleStatistics}). */
    private void showRuleStatistics() {
        if (currentProof == null) {
            return;
        }
        AnalysisResults results = analyzeProof();
        if (results == null) {
            return;
        }
        // HTML table with the four sort buttons of the Swing RuleStatisticsDialog, rendered in
        // the HtmlDialogF WebView seam
        RuleStatisticsDialogF.show(ownerWindow(), results);
    }

    /** @return the window stage to own dialogs, or {@code null} if the panel is not attached */
    private javafx.stage.@Nullable Window ownerWindow() {
        MainWindowF window = extension.window();
        return window != null ? window.getStage() : null;
    }

    /**
     * Opens the "Slice proof to fixed point" dialog (Swing SlicingLeftPanel.java:229-235, the
     * fixed-point button handler): the dialog iterates analyze/slice/load on the current proof
     * until the fixed point is reached. Also the entry point of the
     * {@code key.fx.verify.slicing} harness.
     *
     * @return the opened dialog, or {@code null} if no proof is loaded
     */
    public @Nullable SliceToFixedPointDialogF openSliceToFixedPointDialog() {
        if (currentProof == null) {
            return null;
        }
        SliceToFixedPointDialogF dialog =
            new SliceToFixedPointDialogF(mediator, ownerWindow(), this::analyzeProof,
                this::sliceProof);
        dialog.start(currentProof);
        return dialog;
    }

    /** Show the dependency graph excerpt of the current proof (Swing {@code previewGraph}). */
    private void previewGraph() {
        if (currentProof == null) {
            return;
        }
        DependencyTracker tracker = extension.trackers.get(currentProof);
        if (tracker == null) {
            return;
        }
        String dot = tracker.exportDot(abbreviateFormulas.isSelected(),
            abbreviateChains.isSelected());
        // renders the DOT to a PNG with the graphviz dot binary and shows the image dialog; if
        // the render fails (graphviz missing), the DOT source text dialog is shown instead (the
        // documented fallback, see PreviewDialogF)
        PreviewDialogF.showDot(ownerWindow(), dot);
    }

    /**
     * Analyze the current proof with the selected algorithms (Swing
     * {@code SlicingLeftPanel.analyzeProof}). UI updates are marshalled onto the FX thread
     * because this method may run on a background thread (slicing worker).
     *
     * @return the analysis results, or {@code null} if no proof is loaded or analysis failed
     */
    private @Nullable AnalysisResults analyzeProof() {
        if (currentProof == null) {
            return null;
        }
        try {
            DependencyTracker tracker = extension.trackers.get(currentProof);
            if (tracker == null) {
                return null;
            }
            AnalysisResults results = tracker.analyze(doDependencyAnalysis.isSelected(),
                doDeduplicateRuleApps.isSelected());
            org.key_project.util.javafx.FxUtil.runLater(this::updateUIState);
            return results;
        } catch (Exception e) {
            LOGGER.error("failed to analyze proof", e);
            org.key_project.util.javafx.FxUtil.runLater(() -> showError(e));
        }
        return null;
    }

    /** Slice the current proof (Swing {@code SlicingLeftPanel.sliceProof}). */
    private void sliceProof() {
        if (currentProof == null) {
            return;
        }
        final @Nullable AnalysisResults results = analyzeProof();
        if (results == null) {
            return;
        }
        if (!results.indicateSlicingPotential()) {
            updateUIState();
            return;
        }
        MainWindowF window = extension.window();
        if (window == null) {
            // cannot happen in the running app; guards against unit-test usage
            LOGGER.warn("Slicing requested without an attached main window");
            return;
        }
        final Proof proofToSlice = currentProof;
        Task<Path> task = new Task<>() {
            @Override
            protected Path call() throws Exception {
                // KNOWN-SIMPLIFIED: the Swing original passes a headless
                // DefaultUserInterfaceControl; this port uses the FX window's own user-interface
                // control (a ProblemLoaderControl as well) so the loader callbacks stay FX-safe.
                ProblemLoaderControl control = window.getUserInterfaceControl();
                SlicingProofReplayer replayer = SlicingProofReplayer
                        .constructSlicer(control, proofToSlice, results, null);
                Path proofFile;
                // first slice attempt: leave aggressive de-duplicate on
                if (results.didDeduplicateRuleApps
                        && SlicingSettingsProvider.getSlicingSettings()
                                .getAggressiveDeduplicate(proofToSlice)) {
                    try {
                        proofFile = replayer.slice();
                    } catch (Exception e) {
                        LOGGER.error(
                            "failed to slice using aggressive de-duplication, enabling safe mode ",
                            e);
                        SlicingSettingsProvider.getSlicingSettings()
                                .deactivateAggressiveDeduplicate(proofToSlice);
                        AnalysisResults fixedResults = analyzeProof();
                        proofFile = SlicingProofReplayer
                                .constructSlicer(control, proofToSlice, fixedResults, null)
                                .slice();
                    }
                } else {
                    // second slice attempt / only dependency analysis
                    proofFile = replayer.slice();
                }
                // if this slicing iteration required safe mode to be activated,
                // the next slicing iteration probably also requires safe mode
                if (!SlicingSettingsProvider.getSlicingSettings()
                        .getAggressiveDeduplicate(proofToSlice)) {
                    extension.enableSafeModeForNextProof();
                }
                return proofFile;
            }
        };
        task.setOnSucceeded(event -> {
            // Swing parity (SlicingLeftPanel.java:465, "we do not use UI.loadProblem here to
            // avoid adding the slice to the recent files"): the slice is loaded through the
            // direct loader path, which — unlike openProofFile — does not register the file in
            // the recent-files list.
            window.loadProofFileDirect(task.getValue());
        });
        task.setOnFailed(event -> {
            Throwable error = task.getException() != null ? task.getException()
                    : new IllegalStateException("slicing failed");
            showError(error);
        });
        Thread thread = new Thread(task);
        thread.setDaemon(true);
        thread.start();
    }

    /** Show the given exception in a dialog (Swing {@code SlicingLeftPanel.showError}). */
    private void showError(Throwable exc) {
        LOGGER.error("failed to slice proof", exc);
        Platform.runLater(() -> {
            Alert alert = new Alert(Alert.AlertType.ERROR,
                exc.getMessage() == null ? exc.toString() : exc.getMessage());
            alert.setHeaderText("Error in proof slicing");
            alert.setTitle("Proof Slicing");
            alert.showAndWait();
        });
    }

    private void resetLabels() {
        totalSteps.setText("Total steps: ?");
        usefulSteps.setText("Useful steps: ?");
        totalBranches.setText("Total branches: ?");
        usefulBranches.setText("Useful branches: ?");
        showRuleStatistics.setDisable(true);
        timings.getChildren().clear();
        timingsPane.setVisible(false);
    }

    private void displayResults(@Nullable AnalysisResults results) {
        if (results == null) {
            resetLabels();
            return;
        }
        totalSteps.setText("Total steps: " + results.totalSteps);
        usefulSteps.setText("Useful steps: " + results.usefulStepsNr);
        totalBranches.setText("Total branches: " + results.proof.countBranches());
        usefulBranches.setText("Useful branches: " + results.usefulBranchesNr);
        showRuleStatistics.setDisable(false);
        timings.getChildren().clear();
        // HtmlFactory timings table like the Swing panel (SlicingLeftPanel.java:500-511),
        // rendered in the reused WebView
        List<Collection<String>> rows = results.executionTime.executionTimes()
                .map(action -> (Collection<String>) List.of(action.first,
                    action.second + " ms"))
                .collect(Collectors.toList());
        String html = HtmlFactory.generateTable(
            List.of("Algorithm", "Time"),
            new boolean[] { false, false },
            Optional.of(new String[] { null, "right" }),
            rows,
            null);
        WebView view = timingsView();
        timings.getChildren().add(view);
        view.getEngine().loadContent(html, "text/html");
        timingsPane.setVisible(!rows.isEmpty());
    }

    /**
     * @return the lazily created WebView for the timings table (reused across analyses)
     */
    private WebView timingsView() {
        if (timingsView == null) {
            timingsView = new WebView();
            timingsView.setPrefSize(240, 120);
        }
        return timingsView;
    }

    private void resetGraphLabels() {
        graphNodes.setText("Graph nodes: ?");
        graphEdges.setText("Graph edges: ?");
    }

    private void displayGraphLabels() {
        graphNodes.setText("Graph nodes: " + graphNodesNr);
        graphEdges.setText("Graph edges: " + graphEdgesNr);
    }

    @Override
    public void selectedNodeChanged(KeYSelectionEvent<de.uka.ilkd.key.proof.Node> e) {
        // the panel only reacts to proof switches
    }

    @Override
    public void selectedProofChanged(KeYSelectionEvent<Proof> e) {
        // selection events may be fired from the prover thread (rule applications re-default the
        // selection), so marshal the UI refresh onto the FX thread
        org.key_project.util.javafx.FxUtil.runLater(() -> {
            currentProof = mediator.getSelectedProof();
            resetLabels();
            resetGraphLabels();
            updateUIState();
            DependencyTracker tracker = extension.trackers.get(currentProof);
            if (tracker == null) {
                return;
            }
            if (tracker.getAnalysisResults() != null) {
                displayResults(tracker.getAnalysisResults());
            }
            if (tracker.getDependencyGraph() != null) {
                graphNodesNr = tracker.getDependencyGraph().countNodes();
                graphEdgesNr = tracker.getDependencyGraph().countEdges();
                displayGraphLabels();
            }
        });
    }

    /**
     * Notify the panel that a rule has been applied on the currently opened proof (Swing
     * {@code SlicingLeftPanel.ruleAppliedOnProof}). Called from the prover thread; the update is
     * marshalled onto the FX thread.
     *
     * @param proof proof of the rule application
     * @param tracker dependency tracker of that proof
     */
    public void ruleAppliedOnProof(Proof proof, DependencyTracker tracker) {
        int nodes = tracker.getDependencyGraph().countNodes();
        int edges = tracker.getDependencyGraph().countEdges();
        org.key_project.util.javafx.FxUtil.runLater(() -> {
            currentProof = proof;
            graphNodesNr = nodes;
            graphEdgesNr = edges;
            displayGraphLabels();
            updateUIState();
        });
    }

    @Override
    public void proofPruned(ProofTreeEvent e) {
        ruleAppliedOnProof(e.getSource(), extension.trackers.get(e.getSource()));
    }

    /**
     * Updates the enabled/disabled state of all controls (Swing
     * {@code SlicingLeftPanel.updateUIState}).
     * <p>
     * <b>KNOWN-SIMPLIFIED:</b> the Swing panel greys itself out through the Swing-only
     * {@code SingleCoreFeatureGate}; this port checks the parallel-prover setting directly and
     * disables the panel recursively.
     */
    public void updateUIState() {
        if (!Platform.isFxApplicationThread()) {
            org.key_project.util.javafx.FxUtil.runLater(this::updateUIState);
            return;
        }
        // Proof slicing is single-core only: grey out the whole panel while the multi-core
        // prover is active (its dependency tracker does not record during parallel runs).
        boolean parallelProverActive = ProofIndependentSettings.DEFAULT_INSTANCE
                .getGeneralSettings().isParallelProverEnabled();
        setDisable(parallelProverActive);

        boolean noProofLoaded = currentProof == null;
        if (parallelProverActive) {
            return;
        }
        dotExport.setDisable(noProofLoaded);
        dotExport.setTooltip(noProofLoaded ? nativeTooltip(NO_PROOF_SELECTED) : null);
        showGraphRendering.setDisable(noProofLoaded || !dotAvailable);
        showGraphRendering.setTooltip(noProofLoaded ? nativeTooltip(NO_PROOF_SELECTED)
                : !dotAvailable
                        ? nativeTooltip(
                            "Install graphviz (dot) to enable graph rendering functionality.")
                        : null);
        runAnalysis.setDisable(noProofLoaded);
        runAnalysis.setTooltip(noProofLoaded ? nativeTooltip(NO_PROOF_SELECTED) : null);
        showRuleStatistics.setDisable(noProofLoaded);
        showRuleStatistics.setTooltip(
            noProofLoaded ? nativeTooltip(NO_PROOF_SELECTED)
                    : nativeTooltip("Statistics available after analysis"));
        sliceProof.setDisable(noProofLoaded);
        sliceProof.setTooltip(noProofLoaded ? nativeTooltip(NO_PROOF_SELECTED) : null);
        sliceProofFixedPoint.setDisable(noProofLoaded);
        sliceProofFixedPoint.setTooltip(noProofLoaded ? nativeTooltip(NO_PROOF_SELECTED) : null);
        if (noProofLoaded) {
            return;
        }
        boolean algoSelectionSane = doDependencyAnalysis.isSelected()
                || doDeduplicateRuleApps.isSelected();
        runAnalysis.setDisable(!algoSelectionSane);
        runAnalysis.setTooltip(null);
        sliceProof.setDisable(!algoSelectionSane);
        sliceProof.setTooltip(null);
        sliceProofFixedPoint.setDisable(false);
        sliceProofFixedPoint.setTooltip(nativeTooltip("""
                Slices the proof. The resulting proof is analyzed:
                if more steps may be sliced away, the process repeats.
                Warning: the original proof and intermediate slicing
                iterations are automatically removed!"""));
        DependencyTracker tracker = extension.trackers.get(currentProof);
        if (tracker != null) {
            AnalysisResults results = tracker.getAnalysisResults();
            if (results != null && results.usefulSteps.size() == results.totalSteps) {
                String cannotSliceMinimal = "Cannot remove any proof steps";
                sliceProof.setDisable(true);
                sliceProof.setTooltip(nativeTooltip(cannotSliceMinimal));
                sliceProofFixedPoint.setDisable(true);
                sliceProofFixedPoint.setTooltip(nativeTooltip(cannotSliceMinimal));
            }
        }
    }

    /**
     * Notify the panel that a proof has been disposed (Swing
     * {@code SlicingLeftPanel.proofDisposed}).
     *
     * @param proof disposed proof
     */
    public void proofDisposed(Proof proof) {
        if (proof == currentProof) {
            org.key_project.util.javafx.FxUtil.runLater(() -> {
                currentProof = null;
                updateUIState();
            });
        }
    }

    /**
     * Shows a read-only multi-line text dialog. This is now only the <em>fallback</em> seam of
     * the port: the HTML dialogs ({@link HtmlDialogF}, {@link RuleStatisticsDialogF}) and the
     * graph preview ({@link PreviewDialogF}) have Swing-parity counterparts, and this dialog is
     * used when graphviz rendering fails (see {@link PreviewDialogF#showDot}) and by the
     * context-menu DOT excerpt if the render fails.
     *
     * @param title the dialog title
     * @param text the text to display
     */
    public static void showTextDialog(String title, String text) {
        Platform.runLater(() -> {
            TextArea area = new TextArea(text);
            area.setEditable(false);
            area.setWrapText(false);
            VBox box = new VBox(area);
            VBox.setVgrow(area, Priority.ALWAYS);
            javafx.scene.control.Dialog<Void> dialog = new javafx.scene.control.Dialog<>();
            dialog.setTitle(title);
            dialog.getDialogPane().setContent(box);
            dialog.getDialogPane().setPrefSize(640, 420);
            dialog.getDialogPane().getButtonTypes()
                    .add(javafx.scene.control.ButtonType.CLOSE);
            dialog.show();
        });
    }
}

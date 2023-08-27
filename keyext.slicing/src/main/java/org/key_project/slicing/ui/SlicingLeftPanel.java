/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.slicing.ui;

import java.awt.*;
import java.awt.event.ActionEvent;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.nio.charset.StandardCharsets;
import java.util.Collection;
import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;
import javax.annotation.Nonnull;
import javax.swing.*;
import javax.swing.border.TitledBorder;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.gui.IssueDialog;
import de.uka.ilkd.key.gui.KeYFileChooser;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.extension.api.TabPanel;
import de.uka.ilkd.key.gui.fonticons.IconFactory;
import de.uka.ilkd.key.gui.help.HelpFacade;
import de.uka.ilkd.key.gui.help.HelpInfo;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofTreeEvent;
import de.uka.ilkd.key.proof.ProofTreeListener;
import de.uka.ilkd.key.proof.io.ProblemLoader;
import de.uka.ilkd.key.proof.io.ProblemLoaderControl;

import org.key_project.slicing.DependencyTracker;
import org.key_project.slicing.SlicingExtension;
import org.key_project.slicing.SlicingProofReplayer;
import org.key_project.slicing.SlicingSettingsProvider;
import org.key_project.slicing.analysis.AnalysisResults;
import org.key_project.slicing.util.GenericWorker;
import org.key_project.slicing.util.GraphvizDotExecutor;

import bibliothek.gui.dock.common.action.CAction;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Panel of the proof slicing extension. Contains UI controls to run the various algorithms.
 *
 * @author Arne Keller
 */
@HelpInfo(path = "/user/ProofSlicing/")
public class SlicingLeftPanel extends JPanel implements TabPanel, KeYSelectionListener,
        ProofTreeListener {
    /**
     * The icon of this panel.
     */
    public static final Icon INFO_ICON = IconFactory.SLICE_ICON.get(MainWindow.TAB_ICON_SIZE);
    /**
     * ID of this panel.
     */
    public static final String NAME = "slicingPane";

    /**
     * Logger of this class.
     */
    private static final Logger LOGGER = LoggerFactory.getLogger(SlicingLeftPanel.class);
    /**
     * If set to true, the panel will include information on the current usage of the Java Heap
     * and a button that calls {@link System#gc()}.
     */
    private static final boolean ENABLE_DEBUGGING_UI = false;

    /**
     * KeY mediator instance.
     */
    private final transient KeYMediator mediator;
    /**
     * Extension instance.
     */
    private final transient SlicingExtension extension;
    /**
     * The proof currently shown in the KeY UI.
     */
    private transient Proof currentProof = null;
    /**
     * "Export as DOT" button.
     */
    private JButton dotExport = null;
    /**
     * "Show rendering of graph" button.
     */
    private JButton showGraphRendering = null;
    /**
     * If {@link #ENABLE_DEBUGGING_UI} is true: a button that will call the garbage collector
     */
    private JButton buttonSystemGC = null;
    /**
     * "Slice proof" button.
     */
    private JButton sliceProof = null;
    /**
     * "Slice proof to fixed point" button.
     */
    private JButton sliceProofFixedPoint = null;
    /**
     * "Run analysis" button.
     */
    private JButton runAnalysis = null;
    /**
     * "Show rule statistics" button.
     */
    private JButton showRuleStatistics = null;
    /**
     * Label showing current usage of the Java heap.
     */
    private JLabel memoryStats = null;
    /**
     * Label indicating the number of dependency graph nodes.
     *
     * @see org.key_project.slicing.graph.DependencyGraph
     */
    private JLabel graphNodes = null;
    /**
     * Label indicating the number of dependency graph edges.
     *
     * @see org.key_project.slicing.graph.DependencyGraph
     */
    private JLabel graphEdges = null;
    /**
     * Label showing total number of steps in the analyzed proof.
     */
    private JLabel totalSteps = null;
    /**
     * Label showing number of useful steps as determined by the analysis.
     */
    private JLabel usefulSteps = null;
    /**
     * Label showing total number of branches in the analyzed proof.
     */
    private JLabel totalBranches = null;
    /**
     * Label showing number of useful branches as determined by the analysis.
     */
    private JLabel usefulBranches = null;
    /**
     * Checkbox to abbreviate formulas in DOT output.
     */
    private JCheckBox abbreviateFormulas = null;
    /**
     * Checkbox to enable the dependency analysis algorithm.
     */
    private JCheckBox doDependencyAnalysis = null;
    /**
     * Checkbox to enable rule de-duplication.
     */
    private JCheckBox doDeduplicateRuleApps = null;
    /**
     * Panel showing execution time of the algorithm.
     */
    private JPanel timings = null;

    /**
     * Number of nodes in the dependency graph.
     */
    private int graphNodesNr = 0;
    /**
     * Number of edges in the dependency graph.
     */
    private int graphEdgesNr = 0;
    /**
     * Indicates whether graph statistics ({@link #graphNodes}, {@link #graphEdges}) need to be
     * updated based on {@link #graphNodesNr} and {@link #graphEdgesNr}.
     */
    private boolean updateGraphLabels = false;
    /**
     * Timer to regularly update dependency graph statistics when loading a proof.
     */
    private Timer updateGraphLabelsTimer;

    /**
     * Construct a new panel for this extension.
     *
     * @param mediator the KeY mediator
     * @param extension instance of the extension
     */
    public SlicingLeftPanel(KeYMediator mediator, SlicingExtension extension) {
        super();

        setName(NAME);
        setLayout(new BoxLayout(this, BoxLayout.Y_AXIS));

        buildUI();

        updateUIState();
        invalidate();

        this.mediator = mediator;
        this.extension = extension;

        updateGraphLabelsTimer = new Timer(100, e -> {
            if (updateGraphLabels) {
                displayGraphLabels();
                updateGraphLabelsTimer.stop();
            }
        });
        if (ENABLE_DEBUGGING_UI) {
            Timer updateHeapMemoryTimer = new Timer(100, e -> {
                Runtime runtime = Runtime.getRuntime();
                long total = runtime.totalMemory();
                long used = total - runtime.freeMemory();
                memoryStats.setText(String.format(
                    "Java Heap Usage: %d MB / %d MB", used / 1024 / 1024, total / 1024 / 1024));
            });
            updateHeapMemoryTimer.start();
        }
    }

    private void buildUI() {
        JPanel mainPanel = new JPanel();
        GridBagLayout layout = new GridBagLayout();
        mainPanel.setLayout(layout);

        JPanel panel1 = getDependencyGraphPanel();

        JPanel panel2 = getProofAnalysisPanel();

        JPanel panel3 = new JPanel();
        panel3.setLayout(new BoxLayout(panel3, BoxLayout.Y_AXIS));
        panel3.setBorder(new TitledBorder("Proof slicing"));

        sliceProof = new JButton("Slice proof");
        sliceProof.addActionListener(event -> sliceProof());
        sliceProofFixedPoint = new JButton("Slice proof to fixed point");
        sliceProofFixedPoint.addActionListener(event -> {
            if (currentProof != null) {
                SliceToFixedPointDialog dialog = new SliceToFixedPointDialog(mediator,
                    MainWindow.getInstance(),
                    x -> this.analyzeProof(), this::sliceProof);
                dialog.start(currentProof);
            }
        });
        buttonSystemGC = new JButton("call System.gc()");
        buttonSystemGC.addActionListener(e -> {
            System.gc();
            Runtime.getRuntime().gc();
        });

        sliceProof.setAlignmentX(Component.LEFT_ALIGNMENT);
        sliceProofFixedPoint.setAlignmentX(Component.LEFT_ALIGNMENT);
        panel3.add(sliceProof);
        panel3.add(sliceProofFixedPoint);

        timings = new JPanel();
        timings.setLayout(new BoxLayout(timings, BoxLayout.Y_AXIS));
        timings.setBorder(new TitledBorder("Execution timings"));
        timings.setVisible(false);

        memoryStats = new JLabel("Java Heap Usage: ?");

        panel1.setAlignmentX(Component.LEFT_ALIGNMENT);
        panel2.setAlignmentX(Component.LEFT_ALIGNMENT);
        panel3.setAlignmentX(Component.LEFT_ALIGNMENT);
        buttonSystemGC.setAlignmentX(Component.LEFT_ALIGNMENT);
        memoryStats.setAlignmentX(Component.LEFT_ALIGNMENT);
        timings.setAlignmentX(Component.LEFT_ALIGNMENT);
        mainPanel.add(panel1, gridBagConstraints(0));
        mainPanel.add(panel2, gridBagConstraints(1));
        mainPanel.add(panel3, gridBagConstraints(2));
        mainPanel.add(timings, gridBagConstraints(3));
        if (ENABLE_DEBUGGING_UI) {
            mainPanel.add(buttonSystemGC, gridBagConstraints(4));
            mainPanel.add(memoryStats, gridBagConstraints(5));
        }

        mainPanel.setAlignmentX(Component.LEFT_ALIGNMENT);
        JScrollPane scrollPane = new JScrollPane(mainPanel);
        scrollPane.setAlignmentX(Component.LEFT_ALIGNMENT);
        scrollPane.setAlignmentY(Component.TOP_ALIGNMENT);
        add(scrollPane);
        add(Box.createVerticalGlue());
    }

    private JPanel getProofAnalysisPanel() {
        JPanel panel2 = new JPanel();
        panel2.setLayout(new BoxLayout(panel2, BoxLayout.Y_AXIS));
        panel2.setBorder(new TitledBorder("Proof analysis"));

        totalSteps = new JLabel();
        usefulSteps = new JLabel();
        totalBranches = new JLabel();
        usefulBranches = new JLabel();
        doDependencyAnalysis = new JCheckBox("Dependency analysis");
        doDependencyAnalysis.setSelected(true);
        doDependencyAnalysis.addActionListener(e -> resetLabels());
        doDeduplicateRuleApps = new JCheckBox("De-duplicate rule applications");
        doDeduplicateRuleApps.setSelected(false);
        doDeduplicateRuleApps.addActionListener(e -> resetLabels());
        runAnalysis = new JButton("Run analysis");
        runAnalysis.addActionListener(event -> analyzeProof());
        showRuleStatistics = new JButton("Show rule statistics");
        showRuleStatistics.addActionListener(this::showRuleStatistics);

        panel2.add(totalSteps);
        panel2.add(usefulSteps);
        panel2.add(totalBranches);
        panel2.add(usefulBranches);
        panel2.add(doDependencyAnalysis);
        panel2.add(doDeduplicateRuleApps);
        panel2.add(runAnalysis);
        panel2.add(showRuleStatistics);

        return panel2;
    }

    private JPanel getDependencyGraphPanel() {
        JPanel panel1 = new JPanel();
        panel1.setLayout(new BoxLayout(panel1, BoxLayout.Y_AXIS));
        panel1.setBorder(new TitledBorder("Dependency graph"));

        abbreviateFormulas = new JCheckBox("Abbreviate formulas");
        dotExport = new JButton("Export as DOT");
        dotExport.addActionListener(this::exportDot);
        showGraphRendering = new JButton("Show rendering of graph");
        showGraphRendering.addActionListener(this::previewGraph);

        if (!GraphvizDotExecutor.isDotInstalled()) {
            showGraphRendering.setEnabled(false);
            showGraphRendering.setToolTipText(
                "Install graphviz (dot) to enable graph rendering functionality.");
        }

        graphNodes = new JLabel();
        graphEdges = new JLabel();
        resetGraphLabels();

        abbreviateFormulas.setAlignmentX(Component.LEFT_ALIGNMENT);
        dotExport.setAlignmentX(Component.LEFT_ALIGNMENT);
        showGraphRendering.setAlignmentX(Component.LEFT_ALIGNMENT);

        panel1.add(graphNodes);
        panel1.add(graphEdges);
        panel1.add(abbreviateFormulas);
        panel1.add(dotExport);
        panel1.add(showGraphRendering);

        return panel1;
    }

    private GridBagConstraints gridBagConstraints(int y) {
        GridBagConstraints c = new GridBagConstraints();
        c.gridx = 0;
        c.gridy = y;
        if (y == 0) {
            c.anchor = GridBagConstraints.PAGE_START;
        }
        c.weightx = 1.0;
        c.fill = GridBagConstraints.HORIZONTAL;
        c.insets = new Insets(0, 0, 10, 0);
        return c;
    }

    @Nonnull
    @Override
    public Collection<CAction> getTitleCActions() {
        return List.of(HelpFacade.createHelpButton("user/ProofSlicing/"));
    }

    private void exportDot(ActionEvent event) {
        if (currentProof == null) {
            return;
        }
        KeYFileChooser fileChooser = KeYFileChooser.getFileChooser(
            "Choose filename to save dot file");
        fileChooser.setFileFilter(KeYFileChooser.DOT_FILTER);
        fileChooser.setSelectedFile(new File("export.dot"));
        int result = fileChooser.showSaveDialog((JComponent) event.getSource());
        if (result == JFileChooser.APPROVE_OPTION) {
            File file = fileChooser.getSelectedFile();
            try (BufferedWriter writer = new BufferedWriter(
                new OutputStreamWriter(new FileOutputStream(file), StandardCharsets.UTF_8))) {
                String text = extension.trackers.get(currentProof)
                        .exportDot(abbreviateFormulas.isSelected());
                writer.write(text);
            } catch (IOException e) {
                LOGGER.error("failed to export DOT file", e);
                IssueDialog.showExceptionDialog(MainWindow.getInstance(), e);
            }
        }
    }

    private void showRuleStatistics(ActionEvent e) {
        if (currentProof == null) {
            return;
        }
        AnalysisResults results = this.analyzeProof();
        if (results != null) {
            new RuleStatisticsDialog(
                MainWindow.getInstance(),
                results);
        }
    }

    private void previewGraph(ActionEvent e) {
        if (currentProof == null) {
            return;
        }
        String text = extension.trackers.get(currentProof)
                .exportDot(abbreviateFormulas.isSelected());
        new PreviewDialog(MainWindow.getInstance(), text);
    }

    private AnalysisResults analyzeProof() {
        if (currentProof == null) {
            return null;
        }
        try {
            AnalysisResults results = extension.trackers.get(currentProof).analyze(
                doDependencyAnalysis.isSelected(), doDeduplicateRuleApps.isSelected());
            updateUIState();
            return results;
        } catch (Exception e) {
            LOGGER.error("failed to analyze proof", e);
            SwingUtilities.invokeLater(
                () -> IssueDialog.showExceptionDialog(MainWindow.getInstance(), e));
        }
        return null;
    }

    private void sliceProof() {
        if (currentProof == null) {
            return;
        }
        final AnalysisResults results = analyzeProof();
        if (results == null) {
            return;
        }
        if (!results.indicateSlicingPotential()) {
            updateUIState();
            return;
        }
        new GenericWorker<>(() -> {
            // slice proof with a headless LoaderControl to avoid countless UI redraws
            ProblemLoaderControl control = new DefaultUserInterfaceControl();
            SlicingProofReplayer replayer = SlicingProofReplayer
                    .constructSlicer(control, currentProof, results, mediator.getUI());
            File proofFile;
            // first slice attempt: leave aggressive de-duplicate on
            if (results.didDeduplicateRuleApps
                    && SlicingSettingsProvider.getSlicingSettings()
                            .getAggressiveDeduplicate(currentProof)) {
                try {
                    proofFile = replayer.slice();
                } catch (Exception e) {
                    LOGGER.error(
                        "failed to slice using aggressive de-duplication, enabling safe mode ", e);
                    SlicingSettingsProvider.getSlicingSettings()
                            .deactivateAggressiveDeduplicate(currentProof);
                    AnalysisResults fixedResults = analyzeProof();
                    proofFile = SlicingProofReplayer
                            .constructSlicer(control, currentProof, fixedResults, mediator.getUI())
                            .slice();
                }
            } else {
                // second slice attempt / only dependency analysis
                proofFile = replayer.slice();
            }
            // if this slicing iteration required safe mode to be activated,
            // the next slicing iteration probably also requires safe mode
            if (!SlicingSettingsProvider.getSlicingSettings()
                    .getAggressiveDeduplicate(currentProof)) {
                extension.enableSafeModeForNextProof();
            }
            return proofFile;
        }, proofFile -> {
            // we do not use UI.loadProblem here to avoid adding the slice to the recent files
            ProblemLoader problemLoader =
                mediator.getUI().getProblemLoader(proofFile, null, null, null, mediator);
            // user already knows about any warnings
            problemLoader.setIgnoreWarnings(true);
            problemLoader.runAsynchronously();
        }, this::showError).execute();
    }

    private void showError(Throwable e) {
        LOGGER.error("failed to slice proof ", e);
        SwingUtilities.invokeLater(
            () -> IssueDialog.showExceptionDialog(MainWindow.getInstance(), e));
    }

    private void resetLabels() {
        totalSteps.setText("Total steps: ?");
        usefulSteps.setText("Useful steps: ?");
        totalBranches.setText("Total branches: ?");
        usefulBranches.setText("Useful branches: ?");
        showRuleStatistics.setEnabled(false);
        timings.setVisible(false);
        timings.removeAll();
    }

    private void displayResults(AnalysisResults results) {
        if (results == null) {
            resetLabels();
            return;
        }
        totalSteps.setText("Total steps: " + results.totalSteps);
        usefulSteps.setText("Useful steps: " + results.usefulStepsNr);
        totalBranches.setText("Total branches: " + results.proof.countBranches());
        usefulBranches.setText("Useful branches: " + results.usefulBranchesNr);
        showRuleStatistics.setEnabled(true);
        timings.removeAll();
        List<Collection<String>> coll = results.executionTime.executionTimes()
                .map(action -> (Collection<String>) List.of(action.first,
                    action.second + " ms"))
                .collect(Collectors.toList());
        String html = HtmlFactory.generateTable(
            List.of("Algorithm", "Time"),
            new boolean[] { false, false },
            Optional.of(new String[] { null, "right" }),
            coll,
            null);
        timings.add(HtmlFactory.createComponent(html));
        timings.setVisible(true);
    }

    private void resetGraphLabels() {
        graphNodes.setText("Graph nodes: ?");
        graphEdges.setText("Graph edges: ?");
    }

    private void displayGraphLabels() {
        graphNodes.setText("Graph nodes: " + graphNodesNr);
        graphEdges.setText("Graph edges: " + graphEdgesNr);
    }

    @Nonnull
    @Override
    public String getTitle() {
        return "Proof Slicing";
    }

    @Override
    public Icon getIcon() {
        return INFO_ICON;
    }

    @Nonnull
    @Override
    public JComponent getComponent() {
        return this;
    }

    @Override
    public void selectedProofChanged(KeYSelectionEvent e) {
        currentProof = e.getSource().getSelectedProof();
        resetLabels();
        resetGraphLabels();
        updateUIState();
        var tracker = extension.trackers.get(currentProof);
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
    }

    /**
     * Notify the panel that a rule has been applied on the currently opened proof.
     *
     * @param proof proof
     * @param tracker dependency tracker of that proof
     */
    public void ruleAppliedOnProof(Proof proof, DependencyTracker tracker) {
        currentProof = proof;
        graphNodesNr = tracker.getDependencyGraph().countNodes();
        graphEdgesNr = tracker.getDependencyGraph().countEdges();
        updateGraphLabels = true;
        updateGraphLabelsTimer.start();

        updateUIState();
    }

    @Override
    public void proofPruned(ProofTreeEvent e) {
        ruleAppliedOnProof(e.getSource(), extension.trackers.get(e.getSource()));
    }

    private void updateUIState() {
        boolean noProofLoaded = currentProof == null;
        if (noProofLoaded) {
            String noProof = "No proof selected";
            dotExport.setEnabled(false);
            dotExport.setToolTipText(noProof);
            showGraphRendering.setEnabled(false);
            showGraphRendering.setToolTipText(noProof);
            runAnalysis.setEnabled(false);
            runAnalysis.setToolTipText(noProof);
            showRuleStatistics.setEnabled(false);
            showRuleStatistics.setToolTipText("Statistics available after analysis");
            sliceProof.setEnabled(false);
            sliceProof.setToolTipText(noProof);
            sliceProofFixedPoint.setEnabled(false);
            sliceProofFixedPoint.setToolTipText(noProof);
        } else {
            dotExport.setEnabled(true);
            dotExport.setToolTipText(null);
            showGraphRendering.setEnabled(true);
            showGraphRendering.setToolTipText(null);
            boolean algoSelectionSane = doDependencyAnalysis.isSelected()
                    || doDeduplicateRuleApps.isSelected();
            runAnalysis.setEnabled(algoSelectionSane);
            runAnalysis.setToolTipText(null);
            sliceProof.setEnabled(algoSelectionSane);
            sliceProof.setToolTipText(null);
            sliceProofFixedPoint.setEnabled(true);
            sliceProofFixedPoint.setToolTipText(
                "<html>Slices the proof. "
                    + "The resulting proof is analyzed: "
                    + "if more steps may be sliced away, the process repeats."
                    + "<br>Warning: the original proof and intermediate slicing "
                    + "iterations are automatically removed!</html>");
        }
        if (currentProof != null) {
            DependencyTracker tracker = extension.trackers.get(currentProof);
            if (tracker != null) {
                AnalysisResults results = tracker.getAnalysisResults();
                displayResults(results);
                if (results != null) {
                    if (results.usefulSteps.size() == results.totalSteps) {
                        String cannotSliceMinimal = "Cannot remove any proof steps";
                        sliceProof.setEnabled(false);
                        sliceProof.setToolTipText(cannotSliceMinimal);
                        sliceProofFixedPoint.setEnabled(false);
                        sliceProofFixedPoint.setToolTipText(cannotSliceMinimal);
                    }
                }
            }
        }
    }

    /**
     * Notify the panel that a proof has been disposed.
     *
     * @param proof disposed proof
     */
    public void proofDisposed(Proof proof) {
        if (proof == currentProof) {
            currentProof = null;
            updateUIState();
        }
    }
}

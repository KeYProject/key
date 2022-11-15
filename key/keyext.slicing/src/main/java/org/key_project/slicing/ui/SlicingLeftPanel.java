package org.key_project.slicing.ui;

import bibliothek.gui.dock.common.action.CAction;
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
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofTreeEvent;
import de.uka.ilkd.key.proof.ProofTreeListener;
import de.uka.ilkd.key.util.MiscTools;
import org.key_project.slicing.AnalysisResults;
import org.key_project.slicing.DependencyTracker;
import org.key_project.slicing.SlicingExtension;
import org.key_project.slicing.SlicingProofReplayer;
import org.key_project.slicing.util.GraphvizDotExecutor;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import javax.annotation.Nonnull;
import javax.swing.*;
import javax.swing.border.TitledBorder;
import java.awt.*;
import java.awt.event.ActionEvent;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Collection;
import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;

/**
 * Panel of the proof slicing extension. Contains UI controls to run the various algorithms.
 *
 * @author Arne Keller
 */
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

    private final transient KeYMediator mediator;
    private final transient SlicingExtension extension;
    /**
     * The proof currently shown in the KeY UI.
     */
    private transient Proof currentProof = null;
    /**
     * "Export as DOT" button.
     */
    private final JButton dotExport;
    /**
     * "Show rendering of graph" button.
     */
    private final JButton showGraphRendering;
    /**
     * If {@link #ENABLE_DEBUGGING_UI} is true: a button that will call the garbage collector
     */
    private final JButton buttonSystemGC;
    /**
     * "Slice proof" button.
     */
    private final JButton sliceProof;
    /**
     * "Slice proof to fixed point" button.
     */
    private final JButton sliceProofFixedPoint;
    /**
     * "Run analysis" button.
     */
    private final JButton runAnalysis;
    /**
     * "Show rule statistics" button.
     */
    private final JButton showRuleStatistics;
    private final JLabel memoryStats;
    /**
     * Label indicating the number of dependency graph nodes.
     *
     * @see org.key_project.slicing.graph.DependencyGraph
     */
    private final JLabel graphNodes;
    /**
     * Label indicating the number of dependency graph edges.
     *
     * @see org.key_project.slicing.graph.DependencyGraph
     */
    private final JLabel graphEdges;
    private final JLabel totalSteps;
    private final JLabel usefulSteps;
    private final JLabel totalBranches;
    private final JLabel usefulBranches;
    private final JCheckBox abbreviateFormulas;
    private final JCheckBox doDependencyAnalysis;
    private final JCheckBox doDeduplicateRuleApps;
    private final JPanel timings;

    private int graphNodesNr = 0;
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

        JPanel mainPanel = new JPanel();
        mainPanel.setLayout(new BoxLayout(mainPanel, BoxLayout.Y_AXIS));

        JPanel panel1 = new JPanel();
        panel1.setLayout(new BoxLayout(panel1, BoxLayout.Y_AXIS));
        panel1.setBorder(new TitledBorder("Dependency graph"));

        JPanel panel2 = new JPanel();
        panel2.setLayout(new BoxLayout(panel2, BoxLayout.Y_AXIS));
        panel2.setBorder(new TitledBorder("Proof analysis"));

        JPanel panel3 = new JPanel();
        panel3.setLayout(new BoxLayout(panel3, BoxLayout.Y_AXIS));
        panel3.setBorder(new TitledBorder("Proof slicing"));

        abbreviateFormulas = new JCheckBox("Abbreviate formulas");
        dotExport = new JButton("Export as DOT");
        dotExport.addActionListener(this::exportDot);
        showGraphRendering = new JButton("Show rendering of graph");
        showGraphRendering.addActionListener(this::previewGraph);
        runAnalysis = new JButton("Run analysis");
        runAnalysis.addActionListener(event -> analyzeProof());
        sliceProof = new JButton("Slice proof");
        sliceProof.addActionListener(event -> sliceProof());
        sliceProofFixedPoint = new JButton("Slice proof to fixed point");
        sliceProofFixedPoint.addActionListener(event -> {
            if (currentProof != null) {
                SliceToFixedPointDialog dialog = new SliceToFixedPointDialog(mediator,
                    SwingUtilities.getWindowAncestor(sliceProofFixedPoint),
                    x -> this.analyzeProof(), this::sliceProof);
                dialog.start(currentProof);
            }
        });
        buttonSystemGC = new JButton("call System.gc()");
        buttonSystemGC.addActionListener(e -> {
            System.gc();
            Runtime.getRuntime().gc();
        });
        showRuleStatistics = new JButton("Show rule statistics");
        showRuleStatistics.addActionListener(this::showRuleStatistics);
        graphNodes = new JLabel();
        graphEdges = new JLabel();
        resetGraphLabels();
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

        if (!GraphvizDotExecutor.isDotInstalled()) {
            System.out.println("disabling graph rendering");
            showGraphRendering.setEnabled(false);
            showGraphRendering.setToolTipText(
                "Install graphviz (dot) to enable graph rendering functionality.");
        }

        abbreviateFormulas.setAlignmentX(Component.LEFT_ALIGNMENT);
        dotExport.setAlignmentX(Component.LEFT_ALIGNMENT);
        showGraphRendering.setAlignmentX(Component.LEFT_ALIGNMENT);
        panel1.add(graphNodes);
        panel1.add(graphEdges);
        panel1.add(abbreviateFormulas);
        panel1.add(dotExport);
        panel1.add(showGraphRendering);

        panel2.add(totalSteps);
        panel2.add(usefulSteps);
        panel2.add(totalBranches);
        panel2.add(usefulBranches);
        panel2.add(doDependencyAnalysis);
        panel2.add(doDeduplicateRuleApps);
        panel2.add(runAnalysis);
        panel2.add(showRuleStatistics);

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
        mainPanel.add(panel1);
        mainPanel.add(panel2);
        mainPanel.add(panel3);
        if (ENABLE_DEBUGGING_UI) {
            mainPanel.add(buttonSystemGC);
            mainPanel.add(memoryStats);
        }
        mainPanel.add(timings);

        setLayout(new BorderLayout());
        mainPanel.setAlignmentX(Component.LEFT_ALIGNMENT);
        add(new JScrollPane(mainPanel));

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
                var runtime = Runtime.getRuntime();
                var total = runtime.totalMemory();
                var used = total - runtime.freeMemory();
                memoryStats.setText(String.format(
                    "Java Heap Usage: %d MB / %d MB", used / 1024 / 1024, total / 1024 / 1024));
            });
            updateHeapMemoryTimer.start();
        }
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
                new OutputStreamWriter(new FileOutputStream(file)))) {
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
                SwingUtilities.getWindowAncestor((JComponent) e.getSource()),
                results);
        }
    }

    private void previewGraph(ActionEvent e) {
        if (currentProof == null) {
            return;
        }
        String text = extension.trackers.get(currentProof)
                .exportDot(abbreviateFormulas.isSelected());
        new PreviewDialog(SwingUtilities.getWindowAncestor((JComponent) e.getSource()), text);
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
        AnalysisResults results = analyzeProof();
        if (results == null) {
            return;
        }
        if (!results.indicateSlicingPotential()) {
            updateUIState();
            return;
        }
        try {
            // slice proof with a headless LoaderControl to avoid countless UI redraws
            var control = new DefaultUserInterfaceControl();
            Proof proof = SlicingProofReplayer
                    .constructSlicer(control, currentProof, results, mediator.getUI()).slice();
            Path tempDir = Files.createTempDirectory("KeYslice");
            String filename;
            if (currentProof.getProofFile() != null) {
                filename = MiscTools.removeFileExtension(currentProof.getProofFile().getName());
            } else {
                filename = MiscTools.removeFileExtension(currentProof.name().toString());
            }
            int prevSlice = filename.indexOf("_slice");
            if (prevSlice != -1) {
                int sliceNr = Integer.parseInt(filename.substring(prevSlice + "_slice".length()));
                sliceNr++;
                filename = filename.substring(0, prevSlice) + "_slice" + sliceNr;
            } else {
                filename = filename + "_slice1";
            }
            filename = filename + ".proof";
            File tempFile = tempDir.resolve(filename).toFile();
            proof.saveToFile(tempFile);
            proof.dispose();
            SwingUtilities.invokeLater(() -> mediator.getUI().loadProblem(tempFile));
        } catch (Exception e) {
            LOGGER.error("failed to slice proof", e);
            SwingUtilities.invokeLater(
                () -> IssueDialog.showExceptionDialog(MainWindow.getInstance(), e));
        }
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
        var coll = results.executionTime.executionTimes()
                .map(action -> (Collection<String>) List.of(action.first,
                    "" + action.second + " ms"))
                .collect(Collectors.toList());
        var html = HtmlFactory.generateTable(
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
        boolean proofClosed = currentProof != null && currentProof.closed();
        if (!proofClosed) {
            runAnalysis.setEnabled(false);
            runAnalysis.setToolTipText("Cannot analyse open proofs");
            showRuleStatistics.setEnabled(false);
            showRuleStatistics.setToolTipText("Statistics available after analysis");
            String cannotSlice = "Cannot analyse and slice open proofs";
            sliceProof.setEnabled(false);
            sliceProof.setToolTipText(cannotSlice);
            sliceProofFixedPoint.setEnabled(false);
            sliceProofFixedPoint.setToolTipText(cannotSlice);
        } else {
            boolean algoSelectionSane = doDependencyAnalysis.isSelected()
                    || doDeduplicateRuleApps.isSelected();
            runAnalysis.setEnabled(algoSelectionSane);
            runAnalysis.setToolTipText(null);
            sliceProof.setEnabled(algoSelectionSane);
            sliceProof.setToolTipText(null);
            sliceProofFixedPoint.setEnabled(true);
            sliceProofFixedPoint.setToolTipText(
                "Slices the proof. "
                    + "The resulting proof is analyzed: if more steps may be sliced away, the process repeats."
                    + "Warning: the original proof and intermediate slicing iterations are automatically closed!");
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

    public void proofDisposed(Proof proof) {
        if (proof == currentProof) {
            currentProof = null;
            updateUIState();
        }
    }
}

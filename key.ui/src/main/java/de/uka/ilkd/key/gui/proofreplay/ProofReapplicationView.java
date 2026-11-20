/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.proofreplay;

import java.awt.*;
import java.awt.event.ActionEvent;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;
import java.io.File;
import java.io.IOException;
import java.nio.file.Path;
import java.util.*;
import java.util.List;
import java.util.concurrent.ExecutionException;
import java.util.stream.StreamSupport;
import javax.swing.*;
import javax.swing.filechooser.FileNameExtensionFilter;
import javax.swing.tree.*;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.KeyAction;
import de.uka.ilkd.key.gui.extension.api.TabPanel;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.KeYUserProblemFile;
import de.uka.ilkd.key.proof.io.IntermediatePresentationProofFileParser;
import de.uka.ilkd.key.proof.io.IntermediateProofReplayer;
import de.uka.ilkd.key.proof.io.intermediate.*;
import de.uka.ilkd.key.rule.*;
import de.uka.ilkd.key.settings.DefaultSMTSettings;
import de.uka.ilkd.key.settings.ProofIndependentSMTSettings;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.smt.*;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.OperationContract;

import org.key_project.logic.PosInTerm;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;
import org.key_project.util.collection.Pair;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import static de.uka.ilkd.key.proof.io.IntermediateProofReplayer.constructTacletApp;

/// A Swing-based UI component for viewing KeY proofs and allowing reapplication of subtrees
/// and single rules.
///
/// This view displays the proof tree in a JTree and provides context menus for:
///
/// - Reapplying a single rule at a selected node
/// - Reapplying an entire subtree from a selected node
/// - Pruning the proof to a selected node
///
/// @author Cline
public class ProofReapplicationView extends JPanel implements TabPanel {
    private static final Logger LOGGER = LoggerFactory.getLogger(ProofReapplicationView.class);

    private final MainWindow mainWindow;

    /// The tree model for the proof tree
    private final DefaultTreeModel treeModel =
        new DefaultTreeModel(new DefaultMutableTreeNode("No proof loaded"));

    /// The JTree displaying the proof structure
    private final JTree intermProofTree = new JTree(treeModel);

    /// The mediator for proof operations
    private final KeYMediator mediator;

    /// Creates a new ProofReapplicationView.
    public ProofReapplicationView(MainWindow window, KeYMediator mediator) {
        this.mainWindow = window;
        this.mediator = mediator;
        initComponents();
    }

    /// Initializes the UI components.
    private void initComponents() {
        setLayout(new BorderLayout());
        intermProofTree.getSelectionModel()
                .setSelectionMode(TreeSelectionModel.DISCONTIGUOUS_TREE_SELECTION);
        intermProofTree.setCellRenderer(new ProofTreeNodeRenderer());
        intermProofTree.addMouseListener(new MouseAdapter() {
            @Override
            public void mousePressed(MouseEvent e) {
                if (SwingUtilities.isRightMouseButton(e)) {
                    int row = intermProofTree.getRowForLocation(e.getX(), e.getY());
                    if (row == -1) {
                        // right-click on empty space: show no context menu
                        return;
                    }
                    intermProofTree.setSelectionRow(row);
                    showContextMenu(e.getComponent(), e.getX(), e.getY());
                }
            }
        });

        JScrollPane treeScrollPane = new JScrollPane(intermProofTree);
        add(treeScrollPane, BorderLayout.CENTER);
        add(new JButton(new LoadProofAction()), BorderLayout.NORTH);
    }

    /// Action to load a proof file.

    class LoadProofAction extends KeyAction {
        {
            setName(("Load Proof"));
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            JFileChooser fileChooser = new JFileChooser();
            fileChooser
                    .setFileFilter(new FileNameExtensionFilter("Proof files (*.proof)", "proof"));
            int result = fileChooser.showOpenDialog(ProofReapplicationView.this);
            if (result == JFileChooser.APPROVE_OPTION) {
                loadProof(fileChooser.getSelectedFile());
            }
        }
    }

    /// Action to replay subtree from selected node.
    private AbstractAction createReplaySubtreeAction() {
        AbstractAction replaySubtreeAction = new AbstractAction("Replay Subtree") {
            @Override
            public void actionPerformed(ActionEvent e) {
                // replaySubtree();
            }
        };
        // not implemented at the moment
        replaySubtreeAction.setEnabled(false);
        return replaySubtreeAction;
    }

    /// Action to replay single rule at selected node.
    private KeyAction createReplayRuleAction() {
        return new KeyAction() {
            {
                setName("Replay Rule");
            }

            @Override
            public void actionPerformed(ActionEvent e) {
                // Constructing the rule application (in particular for SMT rules) may launch
                // external solvers which can block for a long time. Replay off the EDT and only
                // touch the UI again in done().
                final var worker = new SwingWorker<Void, Void>() {
                    @Override
                    protected Void doInBackground() {
                        replaySingleRule();
                        return null;
                    }

                    @Override
                    protected void done() {
                        try {
                            get();
                        } catch (InterruptedException ex) {
                            Thread.currentThread().interrupt();
                        } catch (ExecutionException ex) {
                            JOptionPane.showMessageDialog(ProofReapplicationView.this,
                                "Error replaying rule:\n" + ex.getCause().getMessage(),
                                "Replay Error", JOptionPane.ERROR_MESSAGE);
                            LOGGER.warn("Error replaying rule", ex);
                        }
                    }
                };
                worker.execute();
            }
        };
    }

    public void loadProof(File file) {
        try {
            Path filePath = file.toPath();
            KeYUserProblemFile problemFile =
                new KeYUserProblemFile(file.getName(), filePath, null, null);
            IntermediatePresentationProofFileParser fileParser =
                new IntermediatePresentationProofFileParser(mediator.getSelectedProof());
            problemFile.readProof(fileParser);
            var r = fileParser.getResult();

            if (!r.errors().isEmpty()) {
                JOptionPane.showMessageDialog(this,
                    "Errors during parsing:\n" + String.join("\n",
                        r.errors().stream().map(Throwable::getMessage).toArray(String[]::new)),
                    "Parse Errors", JOptionPane.ERROR_MESSAGE);
            }

            LOGGER.debug("Proof replay parse status: {}", r.status());

            // Build the tree representation
            rebuildProofTree(r.parsedResult());

        } catch (IOException ex) {
            JOptionPane.showMessageDialog(this,
                "Error loading proof: " + ex.getMessage(),
                "Load Error", JOptionPane.ERROR_MESSAGE);
            LOGGER.warn("", ex);
        } catch (Exception ex) {
            JOptionPane.showMessageDialog(this,
                "Unexpected error: " + ex.getMessage(),
                "Error", JOptionPane.ERROR_MESSAGE);
            LOGGER.warn("", ex);
        }
    }

    /// Rebuilds the proof tree visualization.
    private void rebuildProofTree(BranchNodeIntermediate branchNodeIntermediate) {
        treeModel.setRoot(new ProofTreeIntermediateNode(branchNodeIntermediate));

        // Expand the first few levels
        for (int i = 0; i < 3; i++) {
            intermProofTree.expandRow(i);
        }
    }

    @Override
    public @NonNull String getTitle() {
        return "Proof Applier";
    }

    @Override
    public @NonNull JComponent getComponent() {
        return this;
    }

    /// Custom cell renderer for the proof tree.
    private class ProofTreeNodeRenderer extends DefaultTreeCellRenderer {
        @Override
        public Component getTreeCellRendererComponent(JTree tree, Object value,
                boolean sel, boolean expanded, boolean leaf, int row, boolean hasFocus) {
            super.getTreeCellRendererComponent(tree, value, sel, expanded, leaf, row, hasFocus);

            if (value instanceof TreeNodeIntermediate<?> ptn) {
                var data = ptn.data;
                if (data instanceof AppNodeIntermediate app) {
                    setToolTipText(app.getIntermediateRuleApp().getRuleName());
                }
                // Color based on node type
                if (ptn.errored)
                    setForeground(Color.RED.darker());
                else if (ptn.applied) {
                    setForeground(Color.GREEN.darker());
                }
            }
            return this;
        }
    }

    /// Shows the context menu at the specified location.
    private void showContextMenu(Component invoker, int x, int y) {
        JPopupMenu popup = new JPopupMenu();
        JMenuItem replaySubtreeItem = new JMenuItem(createReplaySubtreeAction());
        JMenuItem replayRuleItem = new JMenuItem(createReplayRuleAction());

        popup.add(replaySubtreeItem);
        popup.add(replayRuleItem);
        popup.addSeparator();

        // Add separator and rule-specific items
        /*
         * RuleApp app = selectedNode.getAppliedRuleApp();
         * if (app != null) {
         * popup.addSeparator();
         * popup.add("Rule: " + app.rule().name());
         * }
         */
        popup.show(invoker, x, y);
    }

    /*
     * Replay subtree / prune interactions are planned but not yet implemented (see PR #3897).
     */

    /// Replays a single rule stored at the selected node of the loaded (.proof) tree onto the
    /// currently selected node of the interactive proof.
    ///
    /// Runs on the SwingWorker thread started by {@link #createReplayRuleAction()}; all UI
    /// updates are marshalled to the EDT.
    private void replaySingleRule() {

        Proof proof = mediator.getSelectedProof();
        if (proof == null) {
            SwingUtilities
                    .invokeLater(() -> JOptionPane.showMessageDialog(ProofReapplicationView.this,
                        "No proof loaded.", "No Proof", JOptionPane.WARNING_MESSAGE));
            return;
        }

        // obtain selected node from the loaded (.proof) tree
        TreeNodeIntermediate<?> selectedNode =
            (TreeNodeIntermediate<?>) intermProofTree.getLastSelectedPathComponent();
        if (selectedNode == null) {
            // nothing selected, e.g. right-click in empty space
            return;
        }
        if (!(selectedNode.data instanceof AppNodeIntermediate currInterm)) {
            // branch markers are not replayable
            return;
        }

        Node currNode = mediator.getSelectedNode();
        Goal currGoal = mediator.getSelectedGoal();
        if (currNode == null || currGoal == null) {
            // only open goals (leaves) of the interactive proof are valid replay targets
            SwingUtilities
                    .invokeLater(() -> JOptionPane.showMessageDialog(ProofReapplicationView.this,
                        "Select an open goal in the active proof to replay this rule onto.",
                        "No Goal Selected", JOptionPane.WARNING_MESSAGE));
            return;
        }

        // Register name proposals
        proof.getServices().getNameRecorder()
                .setProposals(currInterm.getIntermediateRuleApp().getNewNames());

        if (currInterm.getIntermediateRuleApp() instanceof TacletAppIntermediate appInterm) {

            try {
                TacletApp tacletApp = constructTacletApp(proof, appInterm, currGoal);
                currGoal.apply(tacletApp);

                copyStoredNodeInfo(currNode, currInterm);
                markApplied(selectedNode, true);
            } catch (IntermediateProofReplayer.TacletAppConstructionException | RuntimeException
                    | AssertionError e) {
                markApplied(selectedNode, false);
                throw new RuntimeException(
                    "Replay of rule '" + appInterm.getRuleName() + "' (line "
                        + appInterm.getLineNr() + ") failed: " + e.getMessage(),
                    e);
            }
        } else if (currInterm
                .getIntermediateRuleApp() instanceof BuiltInAppIntermediate appInterm) {

            try {
                IBuiltInRuleApp app = constructBuiltinApp(proof, appInterm, currGoal);
                if (!app.complete()) {
                    app = app.tryToInstantiate(currGoal);
                }
                currGoal.apply(app);
                markApplied(selectedNode, true);
            } catch (IntermediateProofReplayer.BuiltInConstructionException | AssertionError
                    | RuntimeException e) {
                markApplied(selectedNode, false);
                throw new RuntimeException(
                    "Replay of rule '" + appInterm.getRuleName() + "' (line "
                        + appInterm.getLineNr() + ") failed: " + e.getMessage(),
                    e);
            }
        }
    }

    /// Copies stored annotations (notes, interactive/script application flags) to the node of the
    /// interactive proof that the rule was replayed onto. Only invoked after a successful rule
    /// application, and existing notes are never cleared.
    private void copyStoredNodeInfo(Node replayedNode, AppNodeIntermediate storedNode) {
        String notes = storedNode.getNotes();
        SwingUtilities.invokeLater(() -> {
            if (notes != null) {
                replayedNode.getNodeInfo().setNotes(notes);
            }
            replayedNode.getNodeInfo().setInteractiveRuleApplication(
                storedNode.isInteractiveRuleApplication());
            replayedNode.getNodeInfo()
                    .setScriptRuleApplication(storedNode.isScriptRuleApplication());
        });
    }

    /// Marks a node of the stored-proof tree as successfully replayed (green) or failed (red)
    /// and repaints it. Safe to call from any thread; the actual tree update runs on the EDT.
    private void markApplied(TreeNodeIntermediate<?> node, boolean ok) {
        SwingUtilities.invokeLater(() -> {
            if (ok) {
                node.applied = true;
            } else {
                node.errored = true;
            }
            treeModel.nodeChanged(node);
        });
    }

    // TODO: taken and adapted from IntermediateProofReplayer. Should be refactored instead there!
    private static IBuiltInRuleApp constructBuiltinApp(Proof proof,
            BuiltInAppIntermediate currInterm, Goal currGoal)
            throws // IntermediateProofReplayer.SkipSMTRuleException,
            IntermediateProofReplayer.BuiltInConstructionException {

        final String ruleName = currInterm.getRuleName();
        final int currFormula = currInterm.getPosInfo().first;
        final PosInTerm currPosInTerm = currInterm.getPosInfo().second;

        Contract currContract = null;
        ImmutableList<PosInOccurrence> builtinIfInsts = null;

        // Load contracts, if applicable
        if (currInterm.getContract() != null) {
            currContract = proof.getServices().getSpecificationRepository()
                    .getContractByName(currInterm.getContract());
            if (currContract == null) {
                throw new IntermediateProofReplayer.BuiltInConstructionException(
                    "Could not reconstruct the rule application: the stored contract \""
                        + currInterm.getContract()
                        + "\" could not be found in the current specification repository.");
                /*
                 * final ProblemLoaderException e =
                 * new ProblemLoaderException(loader, "Error loading proof: contract \""
                 * + currInterm.getContract() + "\" not found.");
                 * reportError(ERROR_LOADING_PROOF_LINE + ", goal " + currGoal.node().serialNr()
                 * + ", rule " + ruleName + NOT_APPLICABLE, e);
                 */
            }
        }

        // Load ifInsts, if applicable
        if (currInterm.getBuiltInIfInsts() != null) {
            builtinIfInsts = ImmutableList.nil();
            for (final Pair<Integer, PosInTerm> ifInstP : currInterm.getBuiltInIfInsts()) {
                final int currIfInstFormula = ifInstP.first;
                final PosInTerm currIfInstPosInTerm = ifInstP.second;

                try {
                    final PosInOccurrence ifInst =
                        PosInOccurrence.findInSequent(
                            currGoal.sequent(),
                            currIfInstFormula, currIfInstPosInTerm);
                    builtinIfInsts = builtinIfInsts.append(ifInst);
                } catch (RuntimeException | AssertionError e) {
                    // TODO: error reporting
                    throw new RuntimeException("Error loading proof: Line " + currInterm.getLineNr()
                        + ", goal " + currGoal.node().serialNr() + ", rule " + ruleName
                        + " not applicable.", e);
                    /*
                     * reportError(
                     * ERROR_LOADING_PROOF_LINE + "Line " + currInterm.getLineNr() + ", goal "
                     * + currGoal.node().serialNr() + ", rule " + ruleName + NOT_APPLICABLE,
                     * e);
                     */
                }
            }
        }

        final SMTRule smtRule = SMTRule.INSTANCE; // proof.getServices().getProfile().findInstanceFor(SMTRule.class);

        if (smtRule.name().toString().equals(ruleName)) {
            if (!ProofIndependentSettings.DEFAULT_INSTANCE.getSMTSettings().isEnableOnLoad()) {
                // TODO
                // status = SMT_NOT_RUN;
                throw new RuntimeException(
                    "SMT rules can only be replayed if 'SMT solver on load' is enabled.");
            }
            boolean error = false;
            final SMTProblem smtProblem = new SMTProblem(currGoal);
            // default to Z3 because this one most likely was used when saving the proof
            String smtSolver = "Z3";
            try {
                DefaultSMTSettings settings = new DefaultSMTSettings(
                    proof.getSettings().getSMTSettings(),
                    ProofIndependentSettings.DEFAULT_INSTANCE.getSMTSettings(),
                    proof.getSettings().getNewSMTSettings(),
                    proof);

                ProofIndependentSMTSettings smtSettings = ProofIndependentSettings.DEFAULT_INSTANCE
                        .getSMTSettings();
                SolverTypeCollection active = smtSettings.computeActiveSolverUnion();
                SMTAppIntermediate smtAppIntermediate = (SMTAppIntermediate) currInterm;
                String storedSolver = smtAppIntermediate.getSolver();
                if (storedSolver != null && !storedSolver.isEmpty()) {
                    smtSolver = storedSolver;
                }
                // try to find the solver that closed the proof
                for (SolverTypeCollection su : smtSettings.getSolverUnions(true)) {
                    if (su.name().equals(smtSolver)) {
                        active = su;
                        break;
                    }
                }
                ArrayList<SMTProblem> problems = new ArrayList<>();
                problems.add(smtProblem);

                SolverLauncher launcher = new SolverLauncher(settings);
                launcher.launch(active.getTypes(), problems,
                    proof.getServices());
            } catch (Exception e) {
                error = true;
            }
            if (error || smtProblem.getFinalResult()
                    .isValid() != SMTSolverResult.ThreeValuedTruth.VALID) {
                // TODO
                // status = SMT_NOT_RUN;
                throw new RuntimeException(
                    "SMT solver '" + smtSolver + "' did not validate the goal.");
            } else {
                String name = smtProblem.getSuccessfulSolver().name();
                ImmutableList<PosInOccurrence> unsatCore =
                    SMTFocusResults.getUnsatCore(smtProblem);
                if (unsatCore != null) {
                    return smtRule.createApp(name, unsatCore);
                } else {
                    return smtRule.createApp(name);
                }
            }
        }

        IBuiltInRuleApp ourApp;
        PosInOccurrence pos = null;

        if (currFormula != 0) { // otherwise we have no pos
            try {
                pos = PosInOccurrence
                        .findInSequent(currGoal.sequent(), currFormula, currPosInTerm);
            } catch (RuntimeException e) {
                throw new IntermediateProofReplayer.BuiltInConstructionException(
                    "Could not reconstruct the rule application: the stored position (formula "
                        + currFormula + ", term " + currPosInTerm
                        + ") could not be located in the current sequent.",
                    e);
            }
        }

        if (currContract != null) {
            AbstractContractRuleApp<?> contractApp;

            if (currContract instanceof OperationContract) {
                var rule = proof.getServices().getProfile().getUseOperationContractRule();
                contractApp = rule.createApp(pos).setContract(currContract);
            } else {
                var rule = proof.getServices().getProfile().getUseDependencyContractRule();
                contractApp = rule.createApp(pos).setContract(currContract);
                // restore "step" if needed
                var depContractApp = ((UseDependencyContractApp<?>) contractApp);
                if (depContractApp.step() == null) {
                    contractApp = depContractApp.setStep(builtinIfInsts.head());
                }
            }

            if (contractApp.check(currGoal.proof().getServices()) == null) {
                throw new IntermediateProofReplayer.BuiltInConstructionException(
                    "Cannot apply contract: " + currContract);
            } else {
                ourApp = contractApp;
            }

            if (builtinIfInsts != null) {
                ourApp = ourApp.setAssumesInsts(builtinIfInsts);
            }
            return ourApp;
        }

        final ImmutableSet<IBuiltInRuleApp> ruleApps = collectAppsForRule(ruleName, currGoal, pos);
        if (ruleApps.size() != 1) {
            if (ruleApps.size() < 1) {
                throw new IntermediateProofReplayer.BuiltInConstructionException(
                    ruleName + " is missing. Most probably the binary "
                        + "for this built-in rule is not in your path or "
                        + "you do not have the permission to execute it.");
            } else {
                throw new IntermediateProofReplayer.BuiltInConstructionException(
                    ruleName + ": found " + ruleApps.size()
                        + " applications. Don't know what to do !\n" + "@ " + pos);
            }
        }
        ourApp = ruleApps.iterator().next();
        if (ourApp instanceof OneStepSimplifierRuleApp) {
            ((OneStepSimplifierRuleApp) ourApp).restrictAssumeInsts(builtinIfInsts);
        }
        builtinIfInsts = null;
        return ourApp;
    }

    /**
     * Retrieves all registered applications at the given goal and position for the rule
     * corresponding to the given ruleName.
     *
     * @param ruleName Name of the rule to find applications for.
     * @param g Goal to search.
     * @param pos Position of interest in the given goal.
     * @return All matching rule applications at pos in g.
     */
    public static ImmutableSet<IBuiltInRuleApp> collectAppsForRule(String ruleName, Goal g,
            PosInOccurrence pos) {

        ImmutableSet<IBuiltInRuleApp> result = DefaultImmutableSet.nil();

        for (final IBuiltInRuleApp app : g.ruleAppIndex().getBuiltInRules(g, pos)) {
            if (app.rule().name().toString().equals(ruleName)) {
                result = result.add(app);
            }
        }

        return result;
    }
}


abstract class TreeNodeIntermediate<T extends NodeIntermediate> implements TreeNode {
    private @Nullable List<TreeNodeIntermediate<?>> children = null;
    private final TreeNodeIntermediate<?> parent;
    final T data;
    boolean applied = false;
    boolean errored = false;

    TreeNodeIntermediate(@Nullable TreeNodeIntermediate<?> parent, T data) {
        this.parent = parent;
        this.data = data;
    }

    public List<TreeNodeIntermediate<?>> getChildren() {
        if (children == null) {
            if (data.getChildren().size() > 1) {
                children = data.getChildren().stream()
                        .map(it -> it instanceof AppNodeIntermediate app
                                ? new AppIntermediateNode(this, app)
                                : new ProofTreeIntermediateNode(this, (BranchNodeIntermediate) it))
                        .toList();
            } else {
                class DepthWalker implements Iterator<NodeIntermediate> {
                    NodeIntermediate current = data;

                    @Override
                    public boolean hasNext() {
                        return current != null && current.getChildren().size() == 1;
                    }

                    @Override
                    public NodeIntermediate next() {
                        return current = current.getChildren().getFirst();
                    }
                }

                final var walker = new DepthWalker();
                var stream =
                    StreamSupport.stream(Spliterators.spliteratorUnknownSize(walker, 0), false);

                var flat = stream
                        .map(it -> it instanceof AppNodeIntermediate app
                                ? new AppIntermediateNode(this, app)
                                : new ProofTreeIntermediateNode(this, (BranchNodeIntermediate) it))
                        .toList();

                children = new ArrayList<>(flat.size() + 1);
                children.addAll(flat);
                if (walker.current instanceof AppNodeIntermediate branch) {
                    children.add(new AppIntermediateNode(this, branch));
                }
            }
        }
        return children;
    }

    @Override
    public TreeNode getChildAt(int childIndex) {
        return getChildren().get(childIndex);
    }

    @Override
    public int getChildCount() {
        return getChildren().size();
    }

    @Override
    public TreeNode getParent() {
        return parent;
    }

    @Override
    public int getIndex(TreeNode node) {
        return getChildren().indexOf(node);
    }

    @Override
    public boolean getAllowsChildren() {
        return switch (data) {
            case AppNodeIntermediate ignored -> false;
            case BranchNodeIntermediate ignored -> true;
            case null, default -> false;
        };
    }

    @Override
    public boolean isLeaf() {
        return !getAllowsChildren();
    }

    @Override
    public Enumeration<? extends TreeNode> children() {
        return Collections.enumeration(getChildren());
    }
}


class ProofTreeIntermediateNode extends TreeNodeIntermediate<BranchNodeIntermediate> {
    public ProofTreeIntermediateNode(TreeNodeIntermediate<?> parent, BranchNodeIntermediate node) {
        super(parent, node);
    }

    public ProofTreeIntermediateNode(BranchNodeIntermediate node) {
        this(null, node);
    }

    @Override
    public String toString() {
        return "BR: " + data.getBranchTitle();
    }
}


class AppIntermediateNode extends TreeNodeIntermediate<AppNodeIntermediate> {
    public AppIntermediateNode(TreeNodeIntermediate<?> parent, AppNodeIntermediate node) {
        super(parent, node);
    }

    @Override
    public String toString() {
        return "APP: " + data.getIntermediateRuleApp().getRuleName();
    }

    @Override
    public List<TreeNodeIntermediate<?>> getChildren() {
        if (data.getChildren().size() <= 1)
            return Collections.emptyList();
        return super.getChildren();
    }

    @Override
    public boolean getAllowsChildren() {
        return getChildren().size() > 1;
    }
}

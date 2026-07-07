/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.proofreplay;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.KeyAction;
import de.uka.ilkd.key.gui.extension.api.TabPanel;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.TacletIndex;
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
import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;
import org.key_project.logic.PosInTerm;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;
import org.key_project.util.collection.Pair;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import javax.swing.*;
import javax.swing.filechooser.FileNameExtensionFilter;
import javax.swing.tree.*;
import java.awt.*;
import java.awt.event.ActionEvent;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;
import java.io.File;
import java.io.IOException;
import java.nio.file.Path;
import java.util.*;
import java.util.List;
import java.util.stream.StreamSupport;

import static de.uka.ilkd.key.proof.io.IntermediateProofReplayer.constructTacletApp;

/// A Swing-based UI component for viewing KeY proofs and allowing reapplication of subtrees
/// and single rules.
///
/// This view displays the proof tree in a JTree and provides context menus for:
///
///   - Reapplying a single rule at a selected node
///   - Reapplying an entire subtree from a selected node
///   - Pruning the proof to a selected node
///
/// @author Cline
public class ProofReapplicationView extends JPanel implements TabPanel {
    private static final Logger LOGGER = LoggerFactory.getLogger(ProofReapplicationView.class);

    private final MainWindow mainWindow;
    /// The proof currently loaded
    private Proof proof;

    /// The tree model for the proof tree
    private final DefaultTreeModel treeModel = new DefaultTreeModel(new DefaultMutableTreeNode("No proof loaded"));

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
        intermProofTree.getSelectionModel().setSelectionMode(TreeSelectionModel.DISCONTIGUOUS_TREE_SELECTION);
        intermProofTree.setCellRenderer(new ProofTreeNodeRenderer());
        intermProofTree.addTreeSelectionListener(e -> onNodeSelected());
        intermProofTree.addMouseListener(new MouseAdapter() {
            @Override
            public void mousePressed(MouseEvent e) {
                if (SwingUtilities.isRightMouseButton(e)) {
                    int row = intermProofTree.getClosestRowForLocation(e.getX(), e.getY());
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
            fileChooser.setFileFilter(new FileNameExtensionFilter("Proof files (*.proof)", "proof"));
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
                //replaySubtree();
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
                try {
                    replaySingleRule();
                } catch (IntermediateProofReplayer.TacletAppConstructionException ex) {
                    // TODO: error reporting
                    throw new RuntimeException(ex);
                }
            }
        };
    }

    public void loadProof(File file) {
        try {
            Path filePath = file.toPath();
            KeYUserProblemFile problemFile = new KeYUserProblemFile(file.getName(), filePath, null, null);
            IntermediatePresentationProofFileParser fileParser = new IntermediatePresentationProofFileParser(mediator.getSelectedProof());
            problemFile.readProof(fileParser);
            var r = fileParser.getResult();

            if (!r.errors().isEmpty()) {
                JOptionPane.showMessageDialog(this,
                        "Errors during parsing:\n" + String.join("\n",
                                r.errors().stream().map(Throwable::getMessage).toArray(String[]::new)),
                        "Parse Errors", JOptionPane.ERROR_MESSAGE);
            }

            System.out.println(r.status());

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

    /// Counts the number of nodes in the proof tree.
    private int countNodes(Node node) {
        int count = 1;
        for (Node child : node.children()) {
            count += countNodes(child);
        }
        return count;
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
                if (ptn.errored) setForeground(Color.RED.darker());
                else if (ptn.applied) {
                    setForeground(Color.GREEN.darker());
                }
            }
            return this;
        }
    }

    /// Handles node selection in the tree.
    private void onNodeSelected() {
        TreePath path = intermProofTree.getSelectionPath();
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
        /*RuleApp app = selectedNode.getAppliedRuleApp();
        if (app != null) {
            popup.addSeparator();
            popup.add("Rule: " + app.rule().name());
        }*/
        popup.show(invoker, x, y);
    }

    /*
    /// Replays the subtree starting from the selected node.
    private void replaySubtree(TreeNode node) {
        if (proof == null) {
            JOptionPane.showMessageDialog(this,
                    "No proof loaded.",
                    "No Proof", JOptionPane.WARNING_MESSAGE);
            return;
        }

        try {
            // Collect all rule applications from the subtree
            List<RuleApp> ruleApps = collectRuleApps(selectedNode);

            // Prune the proof to the parent of the selected node
            Node parent = selectedNode.parent();
            if (parent != null) {
                proof.pruneProof(parent);

                // Reapply all rules from the collected subtree
                Goal currentGoal = proof.getOpenGoal(parent);
                if (currentGoal != null && !ruleApps.isEmpty()) {
                    // Skip the first rule (it was at the pruned position) and apply the rest
                    for (int i = 1; i < ruleApps.size(); i++) {
                        RuleApp app = ruleApps.get(i);
                        tryReplayRuleAtGoal(currentGoal, app);
                        // Move to next goal after application
                        if (!currentGoal.node().isClosed()) {
                            var nextGoal = proof.getOpenGoal(currentGoal.node());
                            if (nextGoal != null) {
                                currentGoal = nextGoal;
                            }
                        }
                    }
                }

                // Refresh the tree
                rebuildProofTree(r.parsedResult());
                statusLabel.setText("Subtree replayed from node " + selectedNode.serialNr());
            }
        } catch (Exception e) {
            JOptionPane.showMessageDialog(this,
                    "Error replaying subtree: " + e.getMessage(),
                    "Replay Error", JOptionPane.ERROR_MESSAGE);
            statusLabel.setText("Subtree replay failed");
        }
    }*/

    /// Collects all rule applications from a node and its descendants.
    private List<RuleApp> collectRuleApps(Node node) {
        List<RuleApp> result = new ArrayList<>();
        RuleApp app = node.getAppliedRuleApp();
        if (app != null) {
            result.add(app);
        }
        for (Node child : node.children()) {
            result.addAll(collectRuleApps(child));
        }
        return result;
    }

    /// Replays a single rule at the selected node.
    private void replaySingleRule()
        throws IntermediateProofReplayer.TacletAppConstructionException {

        proof = mediator.getSelectedProof();
        if (proof == null) {
            JOptionPane.showMessageDialog(this,
                "No proof loaded.",
                "No Proof", JOptionPane.WARNING_MESSAGE);
            return;
        }

        Node currNode = mediator.getSelectedNode();
        Goal currGoal = mediator.getSelectedGoal();

        // obtain selected node from intermProofTree
        TreeNodeIntermediate<?> selectedNode =
            (TreeNodeIntermediate<?>)intermProofTree.getLastSelectedPathComponent();
        NodeIntermediate currNodeInterm = selectedNode.data;

        /*
        if (n instanceof AppNodeIntermediate nApp) {
            app = nApp.getIntermediateRuleApp();
        } else if (n instanceof BranchNodeIntermediate nBranch) {

        }
        } else {
            // not a replayable rule
            return;
        }*/

        if (currNodeInterm instanceof BranchNodeIntermediate) {
            // not a replayable rule
            return;
        } else if (currNodeInterm instanceof AppNodeIntermediate currInterm) {

            currNode.getNodeInfo().setNotes(currInterm.getNotes());

            // Register name proposals
            proof.getServices().getNameRecorder()
                .setProposals(currInterm.getIntermediateRuleApp().getNewNames());

            if (currInterm.getIntermediateRuleApp() instanceof TacletAppIntermediate appInterm) {

                //try {
                TacletApp tacletApp = constructTacletApp(proof, appInterm, currGoal);
                currGoal.apply(tacletApp);

                /*
                final Iterator<Node> children = currNode.childrenIterator();
                final LinkedList<NodeIntermediate> intermChildren =
                    currInterm.getChildren();

                addChildren(children, intermChildren);*/

                // set information about SUCCESSFUL rule application
                currNode.getNodeInfo().setInteractiveRuleApplication(
                    currInterm.isInteractiveRuleApplication());
                currNode.getNodeInfo()
                    .setScriptRuleApplication(currInterm.isScriptRuleApplication());

                /*
                } catch (Exception | AssertionError e) {
                    reportError("Error loading proof.\n Line " + appInterm.getLineNr()
                        + ", goal " + currGoal.node().serialNr() + ", rule "
                        + appInterm.getRuleName() + NOT_APPLICABLE, e);
                }*/
                selectedNode.applied = true;

            } else if (currInterm.getIntermediateRuleApp() instanceof BuiltInAppIntermediate appInterm) {

                try {
                    IBuiltInRuleApp app = constructBuiltinApp(proof, appInterm, currGoal);
                    if (!app.complete()) {
                        app = app.tryToInstantiate(currGoal);
                    }
                    currGoal.apply(app);

                    /*
                    final Iterator<Node> children = currNode.childrenIterator();
                    LinkedList<NodeIntermediate> intermChildren =
                        currInterm.getChildren();

                    addChildren(children, intermChildren);*/
                //} catch (IntermediateProofReplayer.SkipSMTRuleException e) {
                    // silently continue; status will be reported via polling
                } catch (IntermediateProofReplayer.BuiltInConstructionException | AssertionError
                         | RuntimeException e) {
                    // TODO: error reporting
                    selectedNode.errored = true;
                    throw new RuntimeException("Error loading proof: Line " + appInterm.getLineNr()
                        + ", goal " + currGoal.node().serialNr() + ", rule "
                        + appInterm.getRuleName() + " not applicable.", e);
                    /*reportError(ERROR_LOADING_PROOF_LINE + "Line "
                        + appInterm.getLineNr() + ", goal " + currGoal.node().serialNr()
                        + ", rule " + appInterm.getRuleName() + NOT_APPLICABLE, e);*/
                }
                selectedNode.applied = true;
            }

        /*RuleApp originalApp = selectedNode.getAppliedRuleApp();
        if (originalApp == null) {
            JOptionPane.showMessageDialog(this,
                    "Selected node has no applied rule.",
                    "No Rule", JOptionPane.WARNING_MESSAGE);
            return;
        }

        try {
            // Prune to the selected node's parent
            Node parent = selectedNode.parent();
            if (parent != null) {
                proof.pruneProof(parent);
                Goal goal = proof.getOpenGoal(parent);

                if (goal != null) {
                    tryReplayRuleAtGoal(goal, originalApp);
                }

                rebuildProofTree(r.parsedResult());
                statusLabel.setText("Rule '" + originalApp.rule().name()
                        + "' replayed at node " + parent.serialNr());
            }
        } catch (Exception e) {
            JOptionPane.showMessageDialog(this,
                    "Error replaying rule: " + e.getMessage(),
                    "Replay Error", JOptionPane.ERROR_MESSAGE);
            statusLabel.setText("Rule replay failed");
        }*/
        }
    }

    // TODO: taken and adapted from IntermediateProofReplayer. Should be refactored instead there!
    private static IBuiltInRuleApp constructBuiltinApp(Proof proof, BuiltInAppIntermediate currInterm, Goal currGoal)
        throws //IntermediateProofReplayer.SkipSMTRuleException,
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
                        + currInterm.getContract() + "\" could not be found in the current specification repository.");
                /*final ProblemLoaderException e =
                    new ProblemLoaderException(loader, "Error loading proof: contract \""
                        + currInterm.getContract() + "\" not found.");
                reportError(ERROR_LOADING_PROOF_LINE + ", goal " + currGoal.node().serialNr()
                    + ", rule " + ruleName + NOT_APPLICABLE, e);*/
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
                    reportError(
                        ERROR_LOADING_PROOF_LINE + "Line " + currInterm.getLineNr() + ", goal "
                            + currGoal.node().serialNr() + ", rule " + ruleName + NOT_APPLICABLE,
                        e);*/
                }
            }
        }

        final SMTRule smtRule = SMTRule.INSTANCE; // proof.getServices().getProfile().findInstanceFor(SMTRule.class);

        if (smtRule.name().toString().equals(ruleName)) {
            if (!ProofIndependentSettings.DEFAULT_INSTANCE.getSMTSettings().isEnableOnLoad()) {
                // TODO
                //status = SMT_NOT_RUN;
                throw new RuntimeException();
            }
            boolean error = false;
            final SMTProblem smtProblem = new SMTProblem(currGoal);
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
                String smtSolver = smtAppIntermediate.getSolver();
                if (smtSolver == null || smtSolver.isEmpty()) {
                    // default to Z3 because this one most likely was used when saving the proof
                    smtSolver = "Z3";
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
            if (error || smtProblem.getFinalResult().isValid() != SMTSolverResult.ThreeValuedTruth.VALID) {
                // TODO
                //status = SMT_NOT_RUN;
                throw new RuntimeException();
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
                throw new IntermediateProofReplayer.BuiltInConstructionException("Cannot apply contract: " + currContract);
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
                throw new IntermediateProofReplayer.BuiltInConstructionException(ruleName + ": found " + ruleApps.size()
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

    /// Attempts to replay a rule at the given goal.
    private void tryReplayRuleAtGoal(Goal goal, RuleApp originalApp) {
        Services services = goal.proof().getServices();

        if (originalApp instanceof TacletApp tacletApp) {
            // Find matching taclet applications using the TacletIndex
            TacletIndex tacletIndex = goal.indexOfTaclets();

            // Get all applicable taclets and find matching one
            var allApps = tacletIndex.allNoPosTacletApps();
            NoPosTacletApp matchingApp = null;

            for (NoPosTacletApp candidate : allApps) {
                if (candidate.rule().name().equals(tacletApp.rule().name())) {
                    matchingApp = candidate;
                    break;
                }
            }

            if (matchingApp != null) {
                // Try to match the position if needed
                PosInOccurrence pos = tacletApp.posInOccurrence();
                if (pos != null) {
                    // Find the matching app with position
                    ImmutableList<TacletApp> appsWithPos =
                            ImmutableList.nil();
                    for (TacletApp app : appsWithPos) {
                        if (app.rule().name().equals(tacletApp.rule().name())) {
                            goal.apply(app);
                            return;
                        }
                    }
                } else {
                    goal.apply(matchingApp);
                    return;
                }
            }

            throw new RuntimeException("Could not find matching taclet: "
                    + tacletApp.rule().name());
        } else if (originalApp instanceof IBuiltInRuleApp builtinApp) {
            // Find matching built-in rule applications
            PosInOccurrence pos = builtinApp.posInOccurrence();

            // Collect all built-in rule apps at the position
            ImmutableList<IBuiltInRuleApp> apps =
                    goal.ruleAppIndex().getBuiltInRules(goal, pos);

            IBuiltInRuleApp matchingApp = null;
            for (IBuiltInRuleApp app : apps) {
                if (app.rule().name().equals(builtinApp.rule().name())) {
                    matchingApp = app;
                    break;
                }
            }

            if (matchingApp != null) {
                goal.apply(matchingApp);
            } else {
                throw new RuntimeException("Could not find matching built-in rule: "
                        + builtinApp.rule().name());
            }
        } else {
            throw new RuntimeException("Unsupported rule type: "
                    + originalApp.getClass().getName());
        }
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
            if(data.getChildren().size()>1) {
                 children = data.getChildren().stream().map(it ->
                                it instanceof AppNodeIntermediate app ? new AppIntermediateNode(this, app) :
                                        new ProofTreeIntermediateNode(this, (BranchNodeIntermediate) it))
                        .toList();
            }else {
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

                var flat = stream.map(it ->
                                it instanceof AppNodeIntermediate app ? new AppIntermediateNode(this, app) :
                                        new ProofTreeIntermediateNode(this, (BranchNodeIntermediate) it))
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
        if(data.getChildren().size() <= 1) return Collections.emptyList();
        return super.getChildren();
    }

    @Override
    public boolean getAllowsChildren() {
        return getChildren().size() > 1;
    }
}
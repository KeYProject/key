/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.proofreplay;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.KeyAction;
import de.uka.ilkd.key.gui.extension.api.TabPanel;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.KeYUserProblemFile;
import de.uka.ilkd.key.proof.io.IntermediatePresentationProofFileParser;
import de.uka.ilkd.key.proof.io.intermediate.AppNodeIntermediate;
import de.uka.ilkd.key.proof.io.intermediate.BranchNodeIntermediate;
import de.uka.ilkd.key.proof.io.intermediate.NodeIntermediate;
import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;
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
    private final JTree proofTree = new JTree(treeModel);

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
        proofTree.getSelectionModel().setSelectionMode(TreeSelectionModel.DISCONTIGUOUS_TREE_SELECTION);
        proofTree.setCellRenderer(new ProofTreeNodeRenderer());
        proofTree.addTreeSelectionListener(e -> onNodeSelected());
        proofTree.addMouseListener(new MouseAdapter() {
            @Override
            public void mousePressed(MouseEvent e) {
                if (SwingUtilities.isRightMouseButton(e)) {
                    int row = proofTree.getClosestRowForLocation(e.getX(), e.getY());
                    proofTree.setSelectionRow(row);
                    showContextMenu(e.getComponent(), e.getX(), e.getY());
                }
            }
        });

        JScrollPane treeScrollPane = new JScrollPane(proofTree);
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
        return new AbstractAction("Replay Subtree") {
            @Override
            public void actionPerformed(ActionEvent e) {
                //replaySubtree();
            }
        };
    }

    /// Action to replay single rule at selected node.
    private KeyAction createReplayRuleAction() {
        return new KeyAction() {
            {
                setName("Replay Rule");
            }

            @Override
            public void actionPerformed(ActionEvent e) {
                //replaySingleRule();
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
            proofTree.expandRow(i);
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
        TreePath path = proofTree.getSelectionPath();
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
    }

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
    private void replaySingleRule(ProofTreeIntermediateNode node) {
        if (proof == null) {
            JOptionPane.showMessageDialog(this,
                    "No proof loaded.",
                    "No Proof", JOptionPane.WARNING_MESSAGE);
            return;
        }

        RuleApp originalApp = selectedNode.getAppliedRuleApp();
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
        }
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
    */
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
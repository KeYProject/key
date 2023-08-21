/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.exploration.ui;

import java.awt.*;
import java.awt.event.ActionEvent;
import java.util.*;
import java.util.List;
import javax.annotation.Nonnull;
import javax.annotation.Nullable;
import javax.swing.*;
import javax.swing.tree.*;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.KeyAction;
import de.uka.ilkd.key.gui.extension.api.TabPanel;
import de.uka.ilkd.key.gui.help.HelpFacade;
import de.uka.ilkd.key.gui.help.HelpInfo;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.RuleAppListener;

import org.key_project.exploration.ExplorationNodeData;
import org.key_project.exploration.Icons;

import bibliothek.gui.dock.common.action.CAction;

/**
 * A view that summaries the exploration steps inside a proof.
 *
 * @author Sarah Grebing
 */
@HelpInfo(path = "/Using Key/Exploration/")
public class ExplorationStepsList extends JPanel implements TabPanel {
    private final JLabel hasExplorationSteps = new JLabel();
    private final PruneExplorationAction actionPruneExploration = new PruneExplorationAction();
    private final JumpToNodeAction actionJumpToNode = new JumpToNodeAction();
    private final DefaultListModel<Node> listModelExploration = new DefaultListModel<>();
    private final JList<Node> listExplorations = new JList<>(listModelExploration);
    private final DefaultTreeModel treeModelExploration = new DefaultTreeModel(null);
    private final JTree treeExploration = new JTree(treeModelExploration);
    private final transient KeYMediator mediator;

    private final transient RuleAppListener ruleAppListener = e1 -> {
        createModel(e1.getSource());
        TreePath selectionPath = treeExploration.getSelectionModel().getSelectionPath();
        setTreeExpandedState(treeExploration, true);
        treeExploration.setSelectionPath(selectionPath);
    };

    private transient Proof currentProof;
    private boolean enabled;


    public ExplorationStepsList(MainWindow window) throws HeadlessException {
        this.mediator = window.getMediator();
        initialize();
    }

    /**
     * Sets the shown proof. If null is given the scenery is emptied otherwise the model
     * reconstructed.
     *
     * @param proof a proof or null
     */
    public void setProof(@Nullable Proof proof) {
        if (currentProof != null) {
            currentProof.removeRuleAppListener(ruleAppListener);
        }
        if (proof != null) {
            proof.addRuleAppListener(ruleAppListener);
        }
        currentProof = proof;
        createModel(proof);
    }

    public void setEnabled(boolean enabled) {
        var old = this.enabled;
        this.enabled = enabled;
        if (old != enabled) {
            createModel(currentProof);
        }
    }

    public Proof getProof() { return currentProof; }

    private void createModel(@Nullable Proof model) {
        listModelExploration.clear();
        if (enabled && model != null && !model.isDisposed()) {
            Node root = model.root();
            // build the treemodel
            MyTreeNode rootNode = new MyTreeNode(root);
            treeModelExploration.setRoot(rootNode);
            List<Node> explorationNodes =
                collectAllExplorationSteps(root, treeModelExploration, rootNode);
            explorationNodes.forEach(listModelExploration::addElement);
        } else {
            treeModelExploration.setRoot(null);
        }
        updateLabel();
    }

    private void updateLabel() {
        hasExplorationSteps.setIcon(Icons.EXPLORE.get());
        hasExplorationSteps.setToolTipText("The current proof contains exploratory proof steps.");
        if (listModelExploration.isEmpty()) {
            hasExplorationSteps.setIcon(Icons.EXPLORE_DISABLE.get());
            hasExplorationSteps.setToolTipText(
                "The current proof does not contain any exploratory proof steps.");
        }
    }

    private List<Node> collectAllExplorationSteps(Node root, DefaultTreeModel dtm,
            MyTreeNode rootNode) {
        ArrayList<Node> list = new ArrayList<>();
        findExplorationChildren(root, list, dtm, rootNode);
        return list;
    }

    @Override
    public @Nonnull Collection<CAction> getTitleCActions() {
        return Collections.singleton(HelpFacade.createHelpButton("user/Exploration/"));
    }

    /**
     * Collect nodes inside the proof tree which have an proof exploration.
     * <p>
     * During collection of the nodes, the nodes are grouped in the given TreeModel {@code dtm}
     * </p>
     *
     * @param n start node of exploration indow, KeYMediator mediator) { if (leftPanel == null)
     *        leftPanel = new ExplorationStepsList(window); return Collections.singleton(leftPanel);
     *        }* @param foundNodes filled with found exploration nodes
     * @param dtm a tree model which is filled with nodes
     * @param parent the corresponding entry of {@code n} in the tree model
     */
    private void findExplorationChildren(@Nonnull Node node,
            final @Nonnull ArrayList<Node> foundNodes, @Nonnull DefaultTreeModel dtm,
            @Nonnull MyTreeNode parent) {
        Set<Node> reached = new HashSet<>(512000);
        ArrayDeque<Node> nodes = new ArrayDeque<>(8);
        nodes.add(node);

        // depth-first traversal
        while (!nodes.isEmpty()) {
            Node n = nodes.pollLast();

            ExplorationNodeData explorationNodeData = n.lookup(ExplorationNodeData.class);
            if (explorationNodeData != null && explorationNodeData.getExplorationAction() != null) {
                // exploration found
                MyTreeNode newNode = new MyTreeNode(n);
                dtm.insertNodeInto(newNode, parent, 0);
                parent = newNode;
                foundNodes.add(n);
            }

            reached.add(n);
            for (Node child : n) {
                if (!reached.contains(child)) {
                    nodes.push(child);
                }
            }
        }
    }

    private void initialize() {
        setLayout(new BorderLayout());

        listExplorations.setCellRenderer(new MyCellRenderer());
        listExplorations.addListSelectionListener(e -> {
            if (!e.getValueIsAdjusting()) {
                Node selected = listExplorations.getSelectedValue();
                if (selected != null) {
                    TreePath treePath = getTreePath(selected);
                    if (treePath != null) {
                        treeExploration.setSelectionPath(treePath);
                    }
                    mediator.getSelectionModel().setSelectedNode(selected);
                }
            }
        });

        listExplorations.getSelectionModel().addListSelectionListener(e -> {
            actionJumpToNode.setEnable();
            actionPruneExploration.setEnable();
        });

        actionJumpToNode.setEnable();
        actionPruneExploration.setEnable();

        treeExploration.addTreeSelectionListener(e -> {
            MyTreeNode selectedNode = (MyTreeNode) treeExploration.getLastSelectedPathComponent();
            if (selectedNode != null) {
                mediator.getSelectionModel().setSelectedNode(selectedNode.getData());
                int selectionIndex = getSelectionIndex(selectedNode.getData());
                if (selectionIndex > -1) {
                    listExplorations.setSelectedIndex(selectionIndex);
                }
            }
        });
        treeExploration.setShowsRootHandles(true);
        setTreeExpandedState(treeExploration, true);


        treeExploration.setCellRenderer(new MyTreeCellRenderer());

        JScrollPane p2 = new JScrollPane(listExplorations);
        p2.setBorder(BorderFactory.createTitledBorder("List of Exploration"));
        JScrollPane p1 = new JScrollPane(treeExploration);
        p1.setBorder(BorderFactory.createTitledBorder("Explorations in Proof"));
        JSplitPane root = new JSplitPane(JSplitPane.VERTICAL_SPLIT, p2, p1);
        this.add(root, BorderLayout.CENTER);
        this.add(createBottomPanel(), BorderLayout.SOUTH);
    }

    private JPanel createBottomPanel() {
        JPanel buttonPanel = new JPanel(new FlowLayout(FlowLayout.CENTER, 2, 2));
        buttonPanel.add(new JButton(actionJumpToNode));
        buttonPanel.add(new JButton(actionPruneExploration));
        return buttonPanel;
    }

    @Nonnull
    @Override
    public String getTitle() {
        return "Exploration Steps";
    }

    @Nonnull
    @Override
    public JComponent getComponent() {
        return this;
    }

    // region Tree and ListUtils
    private void setTreeExpandedState(JTree tree, boolean expanded) {
        MyTreeNode node = (MyTreeNode) tree.getModel().getRoot();
        if (node != null) {
            setNodeExpanded(tree, node, expanded);
        }
    }

    private void setNodeExpanded(JTree tree, MyTreeNode node, boolean expanded) {
        ArrayList<MyTreeNode> list = new ArrayList<>();
        if (node.children() != null) {
            Enumeration<TreeNode> children = node.children();
            while (children.hasMoreElements()) {
                list.add((MyTreeNode) children.nextElement());
            }
            list.forEach(myTreeNode -> setNodeExpanded(tree, myTreeNode, expanded));
            if (!expanded && node.isRoot()) {
                return;
            }
            TreePath path = new TreePath(node.getPath());
            if (expanded) {
                tree.expandPath(path);
            } else {
                tree.collapsePath(path);
            }
        }
    }

    private TreePath getTreePath(Node n) {
        MyTreeNode rootNode = (MyTreeNode) treeModelExploration.getRoot();
        Enumeration<TreeNode> treeNodeEnumeration = rootNode.depthFirstEnumeration();
        while (treeNodeEnumeration.hasMoreElements()) {
            TreeNode treeNode = treeNodeEnumeration.nextElement();
            if (((MyTreeNode) treeNode).getData().equals(n)) {
                return new TreePath(treeNode);
            }
        }
        return null;
    }

    private int getSelectionIndex(Node n) {
        for (int i = 0; i < listModelExploration.size(); i++) {
            if (listModelExploration.getElementAt(i).equals(n)) {
                return i;
            }
        }
        return -1;

    }

    public JLabel getHasExplorationSteps() {
        return hasExplorationSteps;
    }

    private static class MyCellRenderer extends DefaultListCellRenderer {
        @Override
        public Component getListCellRendererComponent(JList<?> list, Object value, int index,
                boolean isSelected, boolean cellHasFocus) {
            JLabel lbl = (JLabel) super.getListCellRendererComponent(list, value, index, isSelected,
                cellHasFocus);
            Node n = (Node) value;

            ExplorationNodeData expData = n.lookup(ExplorationNodeData.class);
            if (expData != null && expData.getExplorationAction() != null) {
                lbl.setText(n.serialNr() + " " + expData.getExplorationAction());
            }
            return lbl;

        }
    }

    private static class MyTreeCellRenderer extends DefaultTreeCellRenderer {
        @Override
        public Component getTreeCellRendererComponent(JTree tree, Object value, boolean sel,
                boolean expanded, boolean leaf, int row, boolean hasFocus) {
            JLabel lbl = (JLabel) super.getTreeCellRendererComponent(tree, value, sel, expanded,
                leaf, row, hasFocus);
            MyTreeNode n = (MyTreeNode) value;
            ExplorationNodeData expData = n.getData().lookup(ExplorationNodeData.class);

            if (n.isRoot()) {
                if (expData != null && expData.getExplorationAction() != null) {
                    lbl.setText("Root Node" + n.getData().serialNr() + " "
                        + expData.getExplorationAction());
                } else {
                    lbl.setText("Root Node");
                }
            } else {

                if (expData != null && expData.getExplorationAction() != null) {
                    lbl.setText(n.getData().serialNr() + " " + expData.getExplorationAction());
                }
            }

            return lbl;
        }

    }

    private static class MyTreeNode extends DefaultMutableTreeNode {
        private transient Node data;

        MyTreeNode(Node data) {
            super(data);
            this.data = data;
        }

        public Node getData() {
            return data;
        }

        public void setData(Node data) {
            this.data = data;
        }

        @Override
        public String toString() {
            return Integer.toString(data.serialNr());
        }
    }
    // endregion

    // region Actions
    private class PruneExplorationAction extends KeyAction {
        public PruneExplorationAction() {
            setName("Prune selected exploration");
        }

        public void setEnable() {
            setEnabled(!listExplorations.isSelectionEmpty());
        }

        public void actionPerformed(ActionEvent e) {
            Node selectedValue = listExplorations.getSelectedValue();
            Object lastSelectedPathComponent = treeExploration.getLastSelectedPathComponent();
            Node explorationNode = null;
            if (lastSelectedPathComponent != null) {
                MyTreeNode selectedNode = (MyTreeNode) lastSelectedPathComponent;
                mediator.getUI().getProofControl().pruneTo(selectedNode.getData());
                explorationNode = selectedNode.getData();
                // update tree with current proof
            }
            if (selectedValue != null) {
                mediator.getUI().getProofControl().pruneTo(selectedValue);
                if (explorationNode == null) {
                    explorationNode = selectedValue;
                }
            }

            if (explorationNode != null) {
                ExplorationNodeData lookup = explorationNode.lookup(ExplorationNodeData.class);
                explorationNode.deregister(lookup, ExplorationNodeData.class);
                // update list and tree with current proof
            }
            createModel(mediator.getSelectedProof());
        }
    }

    private class JumpToNodeAction extends KeyAction {
        public JumpToNodeAction() {
            setName("Jump To Node");
        }

        public void setEnable() {
            setEnabled(!listExplorations.isSelectionEmpty());
        }

        public void actionPerformed(ActionEvent e) {
            Node selectedValue = listExplorations.getSelectedValue();
            if (selectedValue != null) {
                mediator.getSelectionModel().setSelectedNode(selectedValue);
            }
        }
    }
    // endregion
}

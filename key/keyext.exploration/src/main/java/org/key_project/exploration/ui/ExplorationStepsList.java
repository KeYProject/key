package org.key_project.exploration.ui;

import bibliothek.gui.dock.common.action.CAction;
import bibliothek.gui.dock.common.action.CButton;
import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.extension.api.TabPanel;
import de.uka.ilkd.key.gui.fonticons.IconFactory;
import de.uka.ilkd.key.gui.help.HelpFacade;
import de.uka.ilkd.key.gui.help.HelpInfo;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.RuleAppListener;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;
import org.key_project.exploration.ExplorationNodeData;
import org.key_project.exploration.Icons;

import javax.swing.*;
import javax.swing.event.TreeSelectionEvent;
import javax.swing.event.TreeSelectionListener;
import javax.swing.tree.*;
import java.awt.*;
import java.util.*;
import java.util.List;

/**
 * A view that summaries the exploration steps inside a proof.
 *
 * @author Sarah Grebing
 */
@HelpInfo(path = "/Using Key/Exploration/")
public class ExplorationStepsList extends JPanel implements TabPanel {
    //private JButton jumpToNode = new JButton("Jump To Node");
    //TODO weigl: should be given via an action


    public JLabel getHasExplorationSteps() {
        return hasExplorationSteps;
    }

    private final JLabel hasExplorationSteps = new JLabel();
    private JButton pruneExploration = new JButton("Prune Selected Exploration Steps");
    private DefaultListModel<Node> listModel = new DefaultListModel<>();
    private DefaultTreeModel dtm = new DefaultTreeModel(null);
    private JPanel buttonPanel = new JPanel();
    private JTree tree;
    private final RuleAppListener ruleAppListener = e1 -> {
        createModel(e1.getSource());
        TreePath selectionPath = tree.getSelectionModel().getSelectionPath();
        setTreeExpandedState(tree, true);
        tree.setSelectionPath(selectionPath);
    };
    private KeYMediator mediator;
    private Proof currentProof;


    public ExplorationStepsList(MainWindow window) throws HeadlessException {
        this.mediator = window.getMediator();
        initialize();
    }

    /**
     * Sets the shown proof. If null is given the scenery is emptied otherwise the
     * model reconstructed.
     *
     * @param proof a proof or null
     */
    public void setProof(@Nullable Proof proof) {
        if (currentProof != null) {
            currentProof.removeRuleAppListener(ruleAppListener);
        }
        if(proof!=null)
            proof.addRuleAppListener(ruleAppListener);
        createModel(proof);
    }

    private void createModel(@Nullable Proof model) {
        listModel.clear();
        if (model != null && !model.isDisposed()) {
            Node root = model.root();
            //build the treemodel
            MyTreeNode rootNode = new MyTreeNode(root);
            dtm.setRoot(rootNode);
            List<Node> explorationNodes = collectAllExplorationSteps(root, dtm, rootNode);
            explorationNodes.forEach(node -> listModel.addElement(node));
        }
        updateLabel();
    }

    private void updateLabel() {
        hasExplorationSteps.setIcon(Icons.EXPLORE.get());
        if(listModel.isEmpty()){
            hasExplorationSteps.setIcon(Icons.EXPLORE_DISABLE.get());
        }
    }

    private List<Node> collectAllExplorationSteps(Node root, DefaultTreeModel dtm, MyTreeNode rootNode) {
        ArrayList<Node> list = new ArrayList<>();
        findExplorationChildren(root, list, dtm, rootNode);
        return list;
    }

    @Override
    public @NotNull Collection<CAction> getTitleCActions() {
        CButton helpButton = new CButton(null, IconFactory.HELP.get());
        helpButton.addActionListener(e -> {
            HelpFacade.openHelp("/Using%20KeY/Exploration/");
        });
        return Collections.singleton(helpButton);
    }

    /**
     * Collect nodes inside the proof tree which have an proof exploration.
     * <p>
     * During collection of the nodes, the nodes are grouped in the given TreeModel {@code dtm}
     * </p>
     *
     * @param n          start node of exploration
     indow, KeYMediator mediator) {
        if (leftPanel == null) leftPanel = new ExplorationStepsList(window);
        return Collections.singleton(leftPanel);
    }* @param foundNodes filled with found exploration nodes
     * @param dtm        a tree model which is filled with nodes
     * @param parent     the corresponding entry of {@code n} in the tree model
     */
    private void findExplorationChildren(@NotNull Node n,
                                         final @NotNull ArrayList<Node> foundNodes,
                                         @NotNull DefaultTreeModel dtm,
                                         @NotNull MyTreeNode parent) {

        ExplorationNodeData explorationNodeData = n.getNodeInfo().get(ExplorationNodeData.class);
        if (explorationNodeData != null && explorationNodeData.getExplorationAction() != null) {
            // exporation found
            MyTreeNode newNode = new MyTreeNode(n);
            dtm.insertNodeInto(newNode, parent, 0);
            parent = newNode;
            foundNodes.add(n);
        }

        if (!n.leaf()) { // has children, then explore them
            for (Node child : n) {
                foundNodes.addAll(collectAllExplorationSteps(child, dtm, parent));
            }
        }
    }

    private void initialize() {
        BorderLayout manager = new BorderLayout();
        this.setLayout(manager);

        //ButtonPanel
        this.buttonPanel.setLayout(new FlowLayout(FlowLayout.LEFT, 2, 2));
        //this.buttonPanel.add(jumpToNode);
        this.buttonPanel.add(pruneExploration);

        JList explorationStepList = new JList<>(listModel);
        tree = new JTree();
        tree.setModel(dtm);

        explorationStepList.setCellRenderer(new MyCellRenderer());

        explorationStepList.addListSelectionListener(e -> {
            if (!e.getValueIsAdjusting()) {
                Node selected = (Node) explorationStepList.getSelectedValue();
                if (selected != null) {
                    TreePath treePath = getTreePath(selected);
                    if (treePath != null) {
                        tree.setSelectionPath(treePath);
                        //tree.addSelectionPath(treePath);
                    }
                    mediator.getSelectionModel().setSelectedNode(selected);

                }
            }
        });
       /* jumpToNode.addActionListener(actionEvent -> {
            Object selectedValue = explorationStepList.getSelectedValue();
            if(selectedValue != null) {
                Node selected = (Node) selectedValue;
                mediator.getSelectionModel().setSelectedNode(selected);
            }

        });*/

        tree.addTreeSelectionListener(new TreeSelectionListener() {

            @Override
            public void valueChanged(TreeSelectionEvent e) {
                MyTreeNode selectedNode = (MyTreeNode) tree.getLastSelectedPathComponent();
                if (selectedNode != null) {
                    mediator.getSelectionModel().setSelectedNode(selectedNode.getData());
                    int selectionIndex = getSelectionIndex(selectedNode.getData());
                    if (selectionIndex > -1) {
                        explorationStepList.setSelectedIndex(selectionIndex);
                    }
                }
            }
        });
        tree.setShowsRootHandles(true);
        setTreeExpandedState(tree, true);

        pruneExploration.addActionListener(actionEvent -> {

            Object selectedValue = explorationStepList.getSelectedValue();

            Object lastSelectedPathComponent = tree.getLastSelectedPathComponent();

            if (lastSelectedPathComponent != null) {
                MyTreeNode selectedNode = (MyTreeNode) tree.getLastSelectedPathComponent();
                mediator.getUI().getProofControl().pruneTo(selectedNode.getData());
                createModel(mediator.getSelectedProof());
            }
            if (selectedValue != null) {
                Node selected = (Node) selectedValue;
                mediator.getUI().getProofControl().pruneTo(selected);
                createModel(mediator.getSelectedProof());
            }
        });


        JTextArea explaination = new JTextArea("Visualization of performed exploration actions. \n" +
                "To jump to a node where the action was applied to select the entry in the list or the tree view.\n" +
                "To prune exploration actions simply select an action and all action below this action " +
                "(visible in the tree visualization) are removed.");
        explaination.setEditable(false);


        JPanel panel = new JPanel();
        panel.setLayout(new BorderLayout());
        panel.add(explaination, BorderLayout.NORTH);
        JScrollPane p2 = new JScrollPane(explorationStepList);
        panel.add(p2, BorderLayout.CENTER);


        tree.setCellRenderer(new MyTreeCellRenderer());
        JScrollPane p1 = new JScrollPane(tree);

        this.add(p1, BorderLayout.CENTER);
        this.add(panel, BorderLayout.NORTH);
        this.add(buttonPanel, BorderLayout.SOUTH);
        this.setVisible(true);
    }

    @NotNull
    @Override
    public String getTitle() {
        return "Exploration Steps";
    }

    @NotNull
    @Override
    public JComponent getComponent() {
        return this;
    }

    //region Tree and ListUtils
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
            Iterator<TreeNode> treeNodeIterator = children.asIterator();
            while (treeNodeIterator.hasNext()) {
                list.add((MyTreeNode) treeNodeIterator.next());
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
        MyTreeNode rootNode = (MyTreeNode) dtm.getRoot();
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
        for (int i = 0; i < listModel.size(); i++) {
            if (listModel.getElementAt(i).equals(n)) {
                return i;
            }
        }
        return -1;

    }

    private static class MyCellRenderer extends DefaultListCellRenderer {
        @Override
        public Component getListCellRendererComponent(JList<?> list, Object value, int index, boolean isSelected, boolean cellHasFocus) {
            JLabel lbl = (JLabel) super.getListCellRendererComponent(list, value, index, isSelected, cellHasFocus);
            Node n = (Node) value;

            ExplorationNodeData expData = n.getNodeInfo().get(ExplorationNodeData.class);
            if (expData != null && expData.getExplorationAction() != null) {
                lbl.setText(n.serialNr() + " " + expData.getExplorationAction());
            }
            return lbl;

        }
    }

    private static class MyTreeCellRenderer extends DefaultTreeCellRenderer {
        @Override
        public Component getTreeCellRendererComponent(JTree tree, Object value, boolean sel, boolean expanded, boolean leaf, int row, boolean hasFocus) {
            JLabel lbl = (JLabel) super.getTreeCellRendererComponent(tree, value, sel, expanded, leaf, row, hasFocus);
            MyTreeNode n = (MyTreeNode) value;
            ExplorationNodeData expData = n.getData().getNodeInfo().get(ExplorationNodeData.class);

            if (n.isRoot()) {
                if (expData != null && expData.getExplorationAction() != null) {
                    lbl.setText("Root Node" + n.getData().serialNr() + " " + expData.getExplorationAction());
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
        private Node data;

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
    }
    //endregion
}

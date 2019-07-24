package org.key_project.exploration.ui;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.extension.api.TabPanel;
import de.uka.ilkd.key.proof.*;
import org.key_project.exploration.ExplorationNodeData;

import javax.swing.*;
import javax.swing.event.*;
import javax.swing.tree.*;
import java.awt.*;
import java.util.*;
import java.util.List;

public class ExplorationStepsList extends JPanel implements TabPanel {
    //private JButton jumpToNode = new JButton("Jump To Node");
    private JButton pruneExploration = new JButton("Prune Selected Exploration Steps");
    private DefaultListModel<Node> listModel = new DefaultListModel<>();
    private DefaultTreeModel dtm = new DefaultTreeModel(null);
    private JPanel buttonPanel = new JPanel();
    private JTree tree;

    private KeYMediator mediator;

    public ExplorationStepsList(MainWindow window) throws HeadlessException {
        this.mediator = window.getMediator();
        initialize();

        mediator.addKeYSelectionListener(new KeYSelectionListener() {
            @Override
            public void selectedNodeChanged(KeYSelectionEvent e) {
                //do nothing because it does not affect this list
            }

            @Override
            public void selectedProofChanged(KeYSelectionEvent e) {
                createModel(e.getSource().getSelectedProof());
                e.getSource().getSelectedProof().addRuleAppListener(new RuleAppListener() {
                    @Override
                    public void ruleApplied(ProofEvent e) {
                        createModel(e.getSource());
                        TreePath selectionPath = tree.getSelectionModel().getSelectionPath();
                        setTreeExpandedState(tree, true);
                        tree.setSelectionPath(selectionPath);
                    }

                });
            }
        });
    }


    public void setProof(Proof proof) {
        createModel(proof);
    }

    private void createModel(Proof model) {
        listModel.clear();
        Node root = model.root();
        //build the treemodel
        MyTreeNode rootNode = new MyTreeNode(root);
        dtm.setRoot(rootNode);
        List<Node> explorationNodes = collectAllExplorationSteps(root, dtm, rootNode);
        explorationNodes.forEach(node -> listModel.addElement(node));


    }

    public List<Node> collectAllExplorationSteps(Node root, DefaultTreeModel dtm, MyTreeNode rootNode) {
        ArrayList<Node> list = new ArrayList<>();
        findExplorationchildren(root, list, dtm, rootNode);
        return list;
    }

    private void findExplorationchildren(Node n, ArrayList<Node> list, DefaultTreeModel dtm, MyTreeNode parent) {
        MyTreeNode currentParent = parent;

        if (n.leaf()) {
            try{
                ExplorationNodeData explorationNodeData = n.getNodeInfo().get(ExplorationNodeData.class);
                if(explorationNodeData != null && explorationNodeData.getExplorationAction() != null) {

                    MyTreeNode newNode = new MyTreeNode(n);
                    dtm.insertNodeInto(newNode, currentParent, 0);
                    list.add(n);
                    return;
                }
            } catch (IllegalStateException e){
                return;
            }
        } else {
            try {
                ExplorationNodeData explorationNodeData = n.getNodeInfo().get(ExplorationNodeData.class);
                if (explorationNodeData != null && explorationNodeData.getExplorationAction() != null) {
                    MyTreeNode newNode = new MyTreeNode(n);
                    dtm.insertNodeInto(newNode, parent, 0);
                    currentParent = newNode;
                    list.add(n);
                }
            } catch (IllegalStateException e) {
                //Do nothing its intended
            }

            Iterator<Node> nodeIterator = n.childrenIterator();
            while (nodeIterator.hasNext()) {
                list.addAll(collectAllExplorationSteps(nodeIterator.next(), dtm, currentParent));
            }
        }

    }


    public void initialize() {
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
        explorationStepList.addListSelectionListener(new ListSelectionListener() {
            @Override
            public void valueChanged(ListSelectionEvent e) {
                if (!e.getValueIsAdjusting()) {
                    final List<Node> selectedValuesList = explorationStepList.getSelectedValuesList();

                    Object selectedValue = explorationStepList.getSelectedValue();
                    if(selectedValue != null) {
                        Node selected = (Node) selectedValue;
                        TreePath treePath = getTreePath(selected);
                        if(treePath != null) {
                            tree.setSelectionPath(treePath);
                            tree.addSelectionPath(treePath);

                        }
                        mediator.getSelectionModel().setSelectedNode(selected);

                    }
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
                if(selectedNode != null){
                    mediator.getSelectionModel().setSelectedNode(selectedNode.getData());
                    int selectionIndex = getSelectionIndex(selectedNode.getData());
                    if(selectionIndex > -1){
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

            if(lastSelectedPathComponent != null){
                MyTreeNode selectedNode = (MyTreeNode) tree.getLastSelectedPathComponent();
                mediator.getUI().getProofControl().pruneTo(selectedNode.getData());
                createModel(mediator.getSelectedProof());
            }
            if(selectedValue != null) {
                Node selected = (Node) selectedValue;
                mediator.getUI().getProofControl().pruneTo(selected);
                createModel(mediator.getSelectedProof());
            }
        });


        JTextArea explaination = new JTextArea("Visualization of performed exploration actions. \n" +
                "To jump to a node where the action was applied to select the entry in the list or the tree view.\n"+
                "To prune explroation actions simply select an action and all action below this action (visible in the tree visualization) are removed.");

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

    @Override
    public String getTitle() {
        return "Exploration Steps";
    }

    @Override
    public JComponent getComponent() {
        return this;
    }

    private class MyCellRenderer extends DefaultListCellRenderer {
        @Override
        public Component getListCellRendererComponent(JList<?> list, Object value, int index, boolean isSelected, boolean cellHasFocus) {
            JLabel listCellRendererComponent = (JLabel) super.getListCellRendererComponent(list, value, index, isSelected, cellHasFocus);
            Node n = (Node) value;

            ExplorationNodeData explorationNodeData = n.getNodeInfo().get(ExplorationNodeData.class);
            if(explorationNodeData != null && explorationNodeData.getExplorationAction() != null) {
                listCellRendererComponent.setText(n.serialNr() + " " + explorationNodeData.getExplorationAction());
            }
            return listCellRendererComponent;

        }
    }

    private class MyTreeCellRenderer extends DefaultTreeCellRenderer {
        @Override
        public Component getTreeCellRendererComponent(JTree tree, Object value, boolean sel, boolean expanded, boolean leaf, int row, boolean hasFocus) {
            JLabel listCellRendererComponent = (JLabel) super.getTreeCellRendererComponent(tree, value, sel, expanded, leaf, row, hasFocus);
            MyTreeNode n = (MyTreeNode) value;
            ExplorationNodeData explorationNodeData = n.getData().getNodeInfo().get(ExplorationNodeData.class);

            if(n.isRoot()){
                if( explorationNodeData != null && explorationNodeData.getExplorationAction() != null) {
                    listCellRendererComponent.setText("Root Node" + n.getData().serialNr() + " " + explorationNodeData.getExplorationAction());
                } else {
                    listCellRendererComponent.setText("Root Node");
                }
            } else {

                if(explorationNodeData!= null && explorationNodeData.getExplorationAction() != null) {
                    listCellRendererComponent.setText(n.getData().serialNr() + " " + explorationNodeData.getExplorationAction());
                }
            }

            return listCellRendererComponent;
        }

    }

    private class MyTreeNode extends DefaultMutableTreeNode {
        private Node data;

        public MyTreeNode(Node data) {
            super(data);
            this.data = data;
        }

        public MyTreeNode(Object userObject, Node data) {
            super(userObject);
            this.data = data;
        }


        public Node getData() {
            return data;
        }

        public void setData(Node data) {
            this.data = data;
        }
    }


//region:Tree and ListUtils

    private void setTreeExpandedState(JTree tree, boolean expanded) {
        MyTreeNode node = (MyTreeNode) tree.getModel().getRoot();
        if(node != null) {
            setNodeExpanded(tree, node, expanded);
        }
    }

    private void setNodeExpanded(JTree tree, MyTreeNode node, boolean expanded) {
        ArrayList<MyTreeNode> list = new ArrayList<>();
        if(node.children() != null) {
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

    private TreePath getTreePath(Node n){
        MyTreeNode rootNode = (MyTreeNode) dtm.getRoot();
        Enumeration<TreeNode> treeNodeEnumeration = rootNode.depthFirstEnumeration();
        while(treeNodeEnumeration.hasMoreElements()){
            TreeNode treeNode = treeNodeEnumeration.nextElement();
            if(((MyTreeNode) treeNode).getData().equals(n)){
                return new TreePath(treeNode);
            }
        }
        return null;
    }

    private int getSelectionIndex(Node n){
        for(int i = 0; i< listModel.size(); i++){
            if(listModel.getElementAt(i).equals(n)){
                return i;
            }
        }
        return -1;

    }
}

package org.key_project.exploration.ui;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.extension.api.TabPanel;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;

import javax.swing.*;
import javax.swing.event.ListSelectionEvent;
import javax.swing.event.ListSelectionListener;
import javax.swing.tree.DefaultMutableTreeNode;
import javax.swing.tree.DefaultTreeCellRenderer;
import javax.swing.tree.DefaultTreeModel;
import java.awt.*;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

public class ExplorationStepsList extends JPanel implements TabPanel {
    private JButton cancelButton = new JButton("Cancel");
    private JButton jumpToNode = new JButton("Jump To Node");
    private JButton pruneExploration = new JButton("Prune Selected Exploration Steps");
    private DefaultListModel<Node> listModel = new DefaultListModel<>();
    private DefaultTreeModel dtm;
    private JPanel buttonPanel = new JPanel();

    public ExplorationStepsList(MainWindow window) throws HeadlessException {
        initialize();
    }

    public void setProof(Proof proof) {
        createListModel(proof);
    }

    private void createListModel(Proof model) {
        listModel.clear();

        Node root = model.root();

        //build the treemodel
        MyTreeNode rootNode = new MyTreeNode(root);
        dtm = new DefaultTreeModel(rootNode);

        List<Node> explorationNodes = collectAllExplorationSteps(root, dtm, rootNode);
        explorationNodes.forEach(node -> listModel.addElement(node));
        System.out.println("explorationNodes = " + explorationNodes);
    }

    public List<Node> collectAllExplorationSteps(Node root, DefaultTreeModel dtm, MyTreeNode rootNode) {
        ArrayList<Node> list = new ArrayList<>();
        findExplorationchildren(root, list, dtm, rootNode);
        return list;
    }

    private void findExplorationchildren(Node n, ArrayList<Node> list, DefaultTreeModel dtm, MyTreeNode parent) {
        if (n.leaf()) {
            if (!n.getNodeInfo().isExploration()) {
                return;
            } else {
                MyTreeNode newNode = new MyTreeNode(n);
                dtm.insertNodeInto(newNode, parent, 0);
                list.add(n);
                return;
            }
        }
        if (n.getNodeInfo().isExploration()) {
            MyTreeNode newNode = new MyTreeNode(n);
            dtm.insertNodeInto(newNode, parent, 0);

            parent = newNode;
            list.add(n);
        }
        Iterator<Node> nodeIterator = n.childrenIterator();

        while (nodeIterator.hasNext()) {
            list.addAll(collectAllExplorationSteps(nodeIterator.next(), dtm, parent));
        }

    }


    public void initialize() {
        BorderLayout manager = new BorderLayout();
        this.setLayout(manager);


        //ButtonPanel
        this.buttonPanel.setLayout(new FlowLayout(FlowLayout.LEFT, 2, 2));
        this.buttonPanel.add(jumpToNode);
        this.buttonPanel.add(pruneExploration);
        this.buttonPanel.add(cancelButton);

        JList explorationStepList = new JList<>(listModel);
        explorationStepList.setCellRenderer(new MyCellRenderer());
        explorationStepList.addListSelectionListener(new ListSelectionListener() {
            @Override
            public void valueChanged(ListSelectionEvent e) {
                if (!e.getValueIsAdjusting()) {
                    final List<Node> selectedValuesList = explorationStepList.getSelectedValuesList();
                    System.out.println(selectedValuesList);
                }
            }
        });

        JTree tree = new JTree(dtm);
        JScrollPane p1 = new JScrollPane(tree);
        JScrollPane p2 = new JScrollPane(explorationStepList);
        tree.setCellRenderer(new MyTreeCellRenderer());
        this.add(p1, BorderLayout.CENTER);
        this.add(p2, BorderLayout.NORTH);
        this.add(buttonPanel, BorderLayout.SOUTH);
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
            listCellRendererComponent.setText(n.serialNr() + " " + n.getNodeInfo().getExplorationAction());
            return listCellRendererComponent;
        }
    }

    private class MyTreeCellRenderer extends DefaultTreeCellRenderer {
        @Override
        public Component getTreeCellRendererComponent(JTree tree, Object value, boolean sel, boolean expanded, boolean leaf, int row, boolean hasFocus) {
            JLabel listCellRendererComponent = (JLabel) super.getTreeCellRendererComponent(tree, value, sel, expanded, leaf, row, hasFocus);
            MyTreeNode n = (MyTreeNode) value;
            listCellRendererComponent.setText(n.getData().serialNr() + " " + n.getData().getNodeInfo().getExplorationAction());
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
}

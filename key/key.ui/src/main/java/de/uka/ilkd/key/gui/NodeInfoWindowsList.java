package de.uka.ilkd.key.gui;

import java.awt.event.WindowAdapter;
import java.awt.event.WindowEvent;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.SortedMap;
import java.util.TreeMap;
import java.util.TreeSet;

import javax.swing.JComponent;
import javax.swing.JScrollPane;
import javax.swing.JTree;
import javax.swing.tree.DefaultMutableTreeNode;
import javax.swing.tree.DefaultTreeModel;
import javax.swing.tree.TreeNode;
import javax.swing.tree.TreeSelectionModel;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.gui.ext.KeYPaneExtension;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofTreeAdapter;
import de.uka.ilkd.key.proof.ProofTreeEvent;

/**
 * A {@link KeYPaneExtension} showing all open {@link NodeInfoWindow}s.
 *
 * @author lanzinger
 */
public class NodeInfoWindowsList implements KeYPaneExtension {

    private Map<Name, DefaultTreeModel> treeModels = new HashMap<>();
    private Map<Name, Set<NodeInfoWindow>> windows = new HashMap<>();

    private JTree tree = new JTree();

    private MainWindow mainWindow;
    private KeYMediator mediator;

    private Name currentProofName;
    private int currentNodeNr;

    @Override
    public void init(MainWindow mainWindow, KeYMediator mediator) {
        this.mainWindow = mainWindow;
        this.mediator = mediator;

        tree.getSelectionModel().setSelectionMode(TreeSelectionModel.SINGLE_TREE_SELECTION);
        tree.setModel(new DefaultTreeModel(new DefaultMutableTreeNode()));
        tree.setEditable(true);
        tree.setShowsRootHandles(true);
        tree.expandRow(0);
        tree.setRootVisible(false);

        tree.addTreeSelectionListener(e -> {
            TreeNode source = (TreeNode) tree.getLastSelectedPathComponent();

            if (source instanceof TreeLeafNode) {
                ((TreeLeafNode) source).win.requestFocus();
            } else if (source instanceof TreeParentNode) {
                mediator.getSelectionModel().setSelectedNode(
                        ((TreeParentNode) source).node);
            }
        });

        mediator.addKeYSelectionListener(new KeYSelectionListener() {

            @Override
            public void selectedProofChanged(KeYSelectionEvent event) {
                Proof currentProof = event.getSource().getSelectedProof();
                currentProofName = currentProof.name();

                if (!treeModels.containsKey(currentProofName)) {
                    treeModels.put(currentProofName, new DefaultTreeModel(new DefaultMutableTreeNode()));

                    currentProof.addRuleAppListener(e -> {
                        //TODO don't do this
                        resetTreeModel(currentProof);
                    });
                    currentProof.addProofTreeListener(new ProofTreeAdapter() {

                        @Override
                        public void proofStructureChanged(ProofTreeEvent e) {
                            resetTreeModel(currentProof);
                        }

                        @Override
                        public void proofPruned(ProofTreeEvent e) {
                            resetTreeModel(currentProof);
                        }

                        @Override
                        public void proofGoalsChanged(ProofTreeEvent e) {
                            resetTreeModel(currentProof);
                        }

                        @Override
                        public void proofExpanded(ProofTreeEvent e) {
                            resetTreeModel(currentProof);
                        }
                    });
                }

                tree.setModel(treeModels.get(currentProofName));
                tree.revalidate();
                tree.repaint();
            }

            @Override
            public void selectedNodeChanged(KeYSelectionEvent event) {
                currentNodeNr = event.getSource().getSelectedNode().serialNr();

                //TODO put currentNodeNr at top of tree or mark it in some way (if it exists)
            }
        });
    }

    @Override
    public String getTitle() {
        return "Open Windows";
    }

    @Override
    public JComponent getComponent() {
        return new JScrollPane(tree);
    }

    /**
     * Register a new {@link NodeInfoWindow}.
     *
     * @param win the window to register.
     */
    void register(NodeInfoWindow win) {
        Proof proof = win.getNode().proof();
        Name proofName = proof.name();

        if (!windows.containsKey(proofName)) {
            windows.put(proofName, new TreeSet<>());
        }

        windows.get(proofName).add(win);

        //TODO don't do this
        resetTreeModel(proof);

        win.addWindowListener(new WindowAdapter() {

           @Override
            public void windowClosed(WindowEvent event) {
                windows.get(proofName).remove(win);

                //TODO don't do this
                resetTreeModel(proof);
            }
        });
    }

    private void resetTreeModel(Proof proof) {
        Name proofName = proof.name();

        DefaultTreeModel model = new DefaultTreeModel(new DefaultMutableTreeNode());
        treeModels.put(proofName, model);

        if (!windows.containsKey(proofName)) {
            windows.put(proofName, new HashSet<>());
        }

        DefaultMutableTreeNode root = ((DefaultMutableTreeNode) model.getRoot());

        SortedMap<String, List<NodeInfoWindow>> winMap = new TreeMap<>();
        SortedMap<String, TreeParentNode> nodeMap = new TreeMap<>();

        for (NodeInfoWindow win : windows.get(proofName)) {
            Node node = win.getNode();
            if (!node.proof().find(node)) {
                node = null;
            }
            String key = nodeToStr(node);

            if (!winMap.containsKey(key)) {
                winMap.put(key, new LinkedList<>());
                nodeMap.put(key, new TreeParentNode(node));
            }

            winMap.get(key).add(win);
        }

        for (String key : winMap.keySet()) {
            TreeParentNode parentNode = nodeMap.get(key);
            model.insertNodeInto(parentNode, root, root.getChildCount());

            for (NodeInfoWindow win : winMap.get(key)) {
                model.insertNodeInto(new TreeLeafNode(win), parentNode, parentNode.getChildCount());
            }
        }

        if (mediator.getSelectedProof().equals(proof)) {
            tree.setModel(treeModels.get(currentProofName));

            for (int i = 0; i < tree.getRowCount(); i++) {
                tree.expandRow(i);
            }

            tree.revalidate();
            tree.repaint();
        }
    }

    private String nodeToStr(Node node) {
        if (node == null) {
            return "<DELETED NODE>";
        } else {
            return node.serialNr() + ": " + node.name();
        }
    }

    private class TreeParentNode extends DefaultMutableTreeNode {

        private Node node;

        private TreeParentNode(Node node) {
            super(nodeToStr(node));
            this.node = node;
        }
    }

    private class TreeLeafNode extends DefaultMutableTreeNode {

        private NodeInfoWindow win;

        private TreeLeafNode(NodeInfoWindow win) {
            super(win.toString());
            this.win = win;
        }
    }
}

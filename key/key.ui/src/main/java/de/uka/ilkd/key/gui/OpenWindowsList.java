package de.uka.ilkd.key.gui;

import java.awt.event.WindowAdapter;
import java.awt.event.WindowEvent;
import java.util.HashMap;
import java.util.Map;

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
import de.uka.ilkd.key.proof.ProofEvent;
import de.uka.ilkd.key.proof.RuleAppListener;

public class OpenWindowsList implements KeYPaneExtension {

    private Map<Name, DefaultTreeModel> treeModels = new HashMap<>();
    private JTree tree = new JTree();

    private Name currentProofName;
    private int currentNodeNr;

    @Override
    public void init(MainWindow mainWindow, KeYMediator mediator) {
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
            }
        });

        mediator.addKeYSelectionListener(new KeYSelectionListener() {

            @Override
            public void selectedProofChanged(KeYSelectionEvent event) {
                Proof currentProof = event.getSource().getSelectedProof();
                currentProofName = currentProof.name();

                if (!treeModels.containsKey(currentProofName)) {
                    treeModels.put(currentProofName, new DefaultTreeModel(new DefaultMutableTreeNode()));

                    currentProof.addRuleAppListener(new RuleAppListener() {

                        @Override
                        public void ruleApplied(ProofEvent e) {
                            // TODO update name of proof node
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

    void register(AdditionalWindow win) {
        Name proofName = win.getNode().proof().name();
        int nodeNr = win.getNode().serialNr();

        if (!treeModels.containsKey(proofName)) {
            treeModels.put(proofName, new DefaultTreeModel(new DefaultMutableTreeNode()));
        }

        DefaultTreeModel model = treeModels.get(proofName);
        DefaultMutableTreeNode root = ((DefaultMutableTreeNode) model.getRoot());
        int count = ((TreeNode) model.getRoot()).getChildCount();

        TreeParentNode parentNode = null;

        for (int i = 0; i <= count; ++i) {
            if (i == count || ((TreeParentNode) root.getChildAt(i)).nodeNr > nodeNr) {
                parentNode = new TreeParentNode(win.getNode());
                model.insertNodeInto(parentNode, root, i);
                model.nodeStructureChanged(root);
                break;
            } else if (((TreeParentNode) root.getChildAt(i)).nodeNr == nodeNr) {
                parentNode = (TreeParentNode) root.getChildAt(i);
                break;
            }
        }

        model.insertNodeInto(new TreeLeafNode(win), parentNode, parentNode.getChildCount());

        tree.revalidate();
        tree.repaint();

        win.addWindowListener(new WindowAdapter() {

           @Override
            public void windowClosed(WindowEvent event) {
                //TODO remove JTree node
            }
        });
    }

    private class TreeParentNode extends DefaultMutableTreeNode {

        private int nodeNr;

        private TreeParentNode(Node node) {
            super(node.serialNr() + ": " + (node.getAppliedRuleApp() == null ? "OPEN GOAL" : node.getAppliedRuleApp().rule().displayName()));
            this.nodeNr = node.serialNr();
        }
    }

    private class TreeLeafNode extends DefaultMutableTreeNode {

        private AdditionalWindow win;

        private TreeLeafNode(AdditionalWindow win) {
            super(win.toString());
            this.win = win;
        }
    }
}

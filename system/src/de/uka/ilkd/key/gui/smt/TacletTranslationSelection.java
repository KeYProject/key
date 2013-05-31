// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 


package de.uka.ilkd.key.gui.smt;

import java.awt.Color;
import java.awt.Component;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;
import java.util.EventObject;

import javax.swing.ButtonGroup;
import javax.swing.JCheckBox;
import javax.swing.JComponent;
import javax.swing.JLabel;
import javax.swing.JOptionPane;
import javax.swing.JPanel;
import javax.swing.JRadioButton;
import javax.swing.JTree;
import javax.swing.ToolTipManager;
import javax.swing.UIManager;
import javax.swing.tree.DefaultMutableTreeNode;
import javax.swing.tree.DefaultTreeCellEditor;
import javax.swing.tree.DefaultTreeCellRenderer;
import javax.swing.tree.TreeCellEditor;
import javax.swing.tree.TreeModel;
import javax.swing.tree.TreeNode;

import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.gui.KeYSelectionEvent;
import de.uka.ilkd.key.gui.KeYSelectionListener;
import de.uka.ilkd.key.proof.TacletIndex;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.taclettranslation.assumptions.SupportedTaclets;
import de.uka.ilkd.key.taclettranslation.assumptions.SupportedTaclets.TreeItem;
import de.uka.ilkd.key.taclettranslation.assumptions.SupportedTaclets.TreeItem.SelectionMode;

interface InfoListener {
        void eventShowInfo(TreeItem item, TreeNode node);
}

public class TacletTranslationSelection {

        
        private DefaultTreeCellRenderer cellRenderer = null;
        private JTree selectionTree = null;

        private static final int INNER_PANEL = 0;

        private static final int LEAF_PANEL = 1;

        private static final int PAINT = 0;

        private static final int EDIT = 1;

        private TreePanel[][] treePanels = new TreePanel[2][2];
        
        private final SMTSettings  smtSettings;
       

        public TacletTranslationSelection(SMTSettings smtSettings) {
                this.smtSettings = smtSettings;
                treePanels[INNER_PANEL][PAINT] = new InnerPanel(smtSettings.getPdSettings().supportedTaclets);
                treePanels[INNER_PANEL][EDIT] = new InnerPanel(smtSettings.getPdSettings().supportedTaclets);
                treePanels[LEAF_PANEL][PAINT] = new LeafPanel(smtSettings.getPdSettings().supportedTaclets);
                treePanels[LEAF_PANEL][EDIT] = new LeafPanel(smtSettings.getPdSettings().supportedTaclets);

        }

        public static KeYSelectionListener getSelectionListener() {
                return LeafPanel.getSelectionListener();
        }

        protected TreeItem treeItem(TreeNode node) {
                return (TreeItem) ((DefaultMutableTreeNode) node)
                                .getUserObject();
        }

        private int getItemHeight(TreeModel model) {
                TreePanel panel1 = new LeafPanel(smtSettings.getPdSettings().supportedTaclets);
                TreePanel panel2 = new InnerPanel(smtSettings.getPdSettings().supportedTaclets);
                return Math.max(panel1.getHeight(), panel2.getHeight());
                // return getItemHeight( (TreeNode)model.getRoot(),0);
        }

        public JTree getSelectionTree() {
                
                if (selectionTree == null) {
                        
                        selectionTree = new JTree();
                        selectionTree.setModel(smtSettings.getPdSettings().supportedTaclets.getTreeModel());
                        selectionTree.setCellRenderer(getTreeCellRenderer());
                        selectionTree.setCellEditor(getTreeCellEditor());
                        selectionTree.setEditable(true);

                        int height = getItemHeight(selectionTree.getModel());

                        selectionTree.setRowHeight(height);

                        ToolTipManager.sharedInstance().registerComponent(
                                        selectionTree);

                }
                return selectionTree;
        }

        private TreeCellEditor getTreeCellEditor() {
                return new DefaultTreeCellEditor(getSelectionTree(),
                                getTreeCellRenderer()) {
                        public Component getTreeCellEditorComponent(JTree t,
                                        Object value, boolean selected,
                                        boolean expanded, boolean leaf, int row) {

                                TreeItem node = (TreeItem) value;

                                TreeItem root = (TreeItem) t.getModel()
                                                .getRoot();
                                return leaf ? treePanels[LEAF_PANEL][EDIT]
                                                .init(node, root, t,smtSettings)
                                                : treePanels[INNER_PANEL][EDIT]
                                                                .init(node,
                                                                                root,
                                                                                t,smtSettings);

                        }

                        public boolean isCellEditable(EventObject arg0) {
                                return true;
                        }
                };
        }

        private DefaultTreeCellRenderer getTreeCellRenderer() {
                if (cellRenderer == null) {
                        cellRenderer = new DefaultTreeCellRenderer() {
                                private static final long serialVersionUID = 1L;

                                public Component getTreeCellRendererComponent(
                                                JTree tree, Object value,
                                                boolean select,
                                                boolean expanded, boolean leaf,
                                                int row, boolean arg6) {
                                        TreeItem node = (TreeItem) value;
                                        TreeItem root = (TreeItem) tree
                                                        .getModel().getRoot();

                                        return leaf ? treePanels[LEAF_PANEL][PAINT]
                                                        .init(node, root, tree, smtSettings)
                                                        : treePanels[INNER_PANEL][PAINT]
                                                                        .init(node,
                                                                                        root,
                                                                                        tree,smtSettings);

                                }
                        };

                }
                return cellRenderer;
        }

}

abstract class TreePanel extends JPanel {

        private static final long serialVersionUID = 1L;
        protected TreeNode root;
        protected JTree tree;

        protected void addComponent(JComponent comp) {
                comp.setBackground(UIManager.getColor("Tree.textBackground"));
                comp.setFont(UIManager.getFont("Tree.font"));
                this.add(comp);
        }



        public int getHeight() {
                return this.getPreferredSize().height;
        }

        protected void newMode(TreeItem node, SelectionMode mode, SupportedTaclets supportedTaclets) {
                
                node.setMode(mode);

                propergateToRoot(node, SelectionMode.user);

                supportedTaclets.validateSelectionModes();

                tree.validate();
                tree.repaint();

        }

        protected abstract JPanel init(TreeItem node, TreeItem rootNode, JTree t, SMTSettings settings);

        protected void propergateToRoot(TreeItem node, SelectionMode mode) {
                TreeItem parent =(TreeItem) node.getParent();
                if (parent != null) {
                        
                        parent.setMode(mode);
                        propergateToRoot(parent, mode);
                }
        }

        protected void propergateToChild(TreeItem node, SelectionMode mode) {

                for (int i = 0; i < node.getChildCount(); i++) {
                        TreeItem child = (TreeItem)node.getChildAt(i);
                        propergateToChild(child, mode);                        
                        child.setMode(mode);
                }
        }

}

class InnerPanel extends TreePanel {

        private static final long serialVersionUID = 1L;
        private JLabel title = new JLabel();
        private JRadioButton radioAll = new JRadioButton("all");
        private JRadioButton radioNothing = new JRadioButton("none");
        private JRadioButton radioUser = new JRadioButton("custom");
        private TreeItem currentNode = null;
        private ButtonGroup buttonGroup = new ButtonGroup();

        public InnerPanel(final SupportedTaclets supportedTaclets) {
                this.setBackground(UIManager.getColor("Tree.textBackground"));
                // this.setLayout(new BoxLayout(this, BoxLayout.X_AXIS));

                addComponent(title);
                addComponent(radioAll);
                addComponent(radioNothing);
                addComponent(radioUser);

                radioUser.setEnabled(false);

                ToolTipManager.sharedInstance().registerComponent(title);

                buttonGroup.add(radioAll);
                buttonGroup.add(radioNothing);
                buttonGroup.add(radioUser);
                radioNothing.setSelected(true);

                radioAll.addActionListener(new ActionListener() {

                        public void actionPerformed(ActionEvent e) {
                                propergateToChild(currentNode,
                                                SelectionMode.all);
                                newMode(currentNode, SelectionMode.all,supportedTaclets);

                        }
                });

                radioNothing.addActionListener(new ActionListener() {

                        public void actionPerformed(ActionEvent e) {
                                propergateToChild(currentNode,
                                                SelectionMode.nothing);
                                newMode(currentNode, SelectionMode.nothing,supportedTaclets);

                        }
                });
        }

        @Override
        protected JPanel init(TreeItem node, TreeItem rootNode, JTree t, SMTSettings settings) {

                currentNode = node;
                root = rootNode;
                this.tree = t;
                title.setText(currentNode.toString() + ": ");
                

                switch (currentNode.getMode()) {
                case all:
                        radioAll.setSelected(true);

                        break;
                case nothing:
                        radioNothing.setSelected(true);

                        break;

                case user:
                        radioAll.setSelected(false);
                        radioNothing.setSelected(false);
                        radioUser.setSelected(true);

                        break;
                }

                return this;

        }
}

class LeafPanel extends TreePanel {

        private static TacletIndex index;
        private static SelectionListener listener = new SelectionListener();
        private static final long serialVersionUID = 1L;
        private TreeItem currentNode = null;
        private JCheckBox tacletName = new JCheckBox();
        private JLabel infoButton = new JLabel("<html><U>info</html>");
        private JLabel genericLabel = new JLabel();

        public static KeYSelectionListener getSelectionListener() {
                return listener;
        }

        private static class SelectionListener implements KeYSelectionListener {

                /** focused node has changed */
                public void selectedNodeChanged(KeYSelectionEvent e) {
                        react(e);
                }

                private void react(KeYSelectionEvent e) {
                        if (e.getSource().getSelectedProof() != null
                                        && e.getSource().getSelectedGoal() != null) {
                                index = e.getSource().getSelectedGoal()
                                                .indexOfTaclets();
                        } else {
                                index = null;
                        }
                }

                /**
                 * the selected proof has changed (e.g. a new proof has been
                 * loaded)
                 */
                public void selectedProofChanged(KeYSelectionEvent e) {
                        react(e);
                }

        }

        public LeafPanel(final SupportedTaclets supportedTaclets) {
                this.setBackground(UIManager.getColor("Tree.textBackground"));
                addComponent(tacletName);
                addComponent(infoButton);
                addComponent(genericLabel);
                ToolTipManager.sharedInstance().registerComponent(tacletName);
                infoButton.setForeground(Color.BLUE);

                tacletName.addActionListener(new ActionListener() {

                        public void actionPerformed(ActionEvent event) {
                                newMode(currentNode,
                                                tacletName.isSelected() ? SelectionMode.all
                                                                : SelectionMode.nothing,supportedTaclets);
                                // selected(title.isSelected());
                                tree.repaint();

                        }

                });
                infoButton.addMouseListener(new MouseAdapter() {

                        @Override
                        public void mouseClicked(MouseEvent e) {

                                showInfo(currentNode);
                                super.mouseClicked(e);
                        }
                });

        }

        private void showInfo(TreeItem item) {
                if (index == null) {
                        JOptionPane.showMessageDialog(
                                        this,
                                        "You must load a proof to make the"
                                                        + " information for this taclet available.",
                                        "Taclet View",
                                        JOptionPane.CLOSED_OPTION);
                        return;
                }
                final ImmutableSet<NoPosTacletApp> apps = index
                                .allNoPosTacletApps();
                for (final NoPosTacletApp app : apps) {
                        if (app.taclet().name().toString()
                                        .equals(item.toString())) {
                                // TODO uncomment
                                // TacletView.getInstance().showTacletView(app.taclet(),
                                // true);
                                break;
                        }

                }

        }

        @Override
        protected JPanel init(TreeItem node, TreeItem r, JTree t, SMTSettings smtSettings) {
                
                int max = smtSettings != null ? smtSettings.getMaxNumberOfGenerics() :0;
                currentNode = node;
                this.tree = t;
                this.root = r;
                tacletName.setText(node.toString());
                tacletName.setSelected(node.getMode() == SelectionMode.all);
                int count = node.getGenericCount();
                if (count > 0) {
                        genericLabel.setVisible(true);
                        if (max < count) {
                                genericLabel.setForeground(Color.RED);
                                genericLabel.setText("too many generic sorts: "
                                                + count);
                        } else {
                                genericLabel.setForeground(Color.GREEN);
                                genericLabel.setText("generic sorts: " + count);
                        }

                } else {
                        genericLabel.setVisible(false);
                }

                return this;
        }

}

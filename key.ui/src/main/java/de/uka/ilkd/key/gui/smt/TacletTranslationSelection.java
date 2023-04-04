package de.uka.ilkd.key.gui.smt;

import java.awt.*;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;
import java.util.Set;
import javax.swing.*;
import javax.swing.tree.TreeNode;

import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.proof.TacletIndex;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.settings.DefaultSMTSettings;
import de.uka.ilkd.key.taclettranslation.assumptions.SupportedTaclets;
import de.uka.ilkd.key.taclettranslation.assumptions.SupportedTaclets.TreeItem;
import de.uka.ilkd.key.taclettranslation.assumptions.SupportedTaclets.TreeItem.SelectionMode;


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

    protected abstract JPanel init(TreeItem node, TreeItem rootNode, JTree t,
            DefaultSMTSettings settings);

    protected void propergateToRoot(TreeItem node, SelectionMode mode) {
        TreeItem parent = (TreeItem) node.getParent();
        if (parent != null) {

            parent.setMode(mode);
            propergateToRoot(parent, mode);
        }
    }

    protected void propergateToChild(TreeItem node, SelectionMode mode) {

        for (int i = 0; i < node.getChildCount(); i++) {
            TreeItem child = (TreeItem) node.getChildAt(i);
            propergateToChild(child, mode);
            child.setMode(mode);
        }
    }

}


class InnerPanel extends TreePanel {

    private static final long serialVersionUID = 1L;
    private final JLabel title = new JLabel();
    private final JRadioButton radioAll = new JRadioButton("all");
    private final JRadioButton radioNothing = new JRadioButton("none");
    private final JRadioButton radioUser = new JRadioButton("custom");
    private TreeItem currentNode = null;
    private final ButtonGroup buttonGroup = new ButtonGroup();

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

        radioAll.addActionListener(e -> {
            propergateToChild(currentNode, SelectionMode.all);
            newMode(currentNode, SelectionMode.all, supportedTaclets);

        });

        radioNothing.addActionListener(e -> {
            propergateToChild(currentNode, SelectionMode.nothing);
            newMode(currentNode, SelectionMode.nothing, supportedTaclets);

        });
    }

    @Override
    protected JPanel init(TreeItem node, TreeItem rootNode, JTree t, DefaultSMTSettings settings) {

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
    private static final SelectionListener listener = new SelectionListener();
    private static final long serialVersionUID = 1L;
    private TreeItem currentNode = null;
    private final JCheckBox tacletName = new JCheckBox();
    private final JLabel infoButton = new JLabel("<html><U>info</html>");
    private final JLabel genericLabel = new JLabel();

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
                index = e.getSource().getSelectedGoal().indexOfTaclets();
            } else {
                index = null;
            }
        }

        /**
         * the selected proof has changed (e.g. a new proof has been loaded)
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

        tacletName.addActionListener(event -> {
            newMode(currentNode,
                tacletName.isSelected() ? SelectionMode.all : SelectionMode.nothing,
                supportedTaclets);
            // selected(title.isSelected());
            tree.repaint();

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
            JOptionPane.showMessageDialog(this,
                "You must load a proof to make the" + " information for this taclet available.",
                "Taclet View", JOptionPane.CLOSED_OPTION);
            return;
        }
        final Set<NoPosTacletApp> apps = index.allNoPosTacletApps();
        for (final NoPosTacletApp app : apps) {
            if (app.taclet().name().toString().equals(item.toString())) {
                // TODO uncomment
                // TacletView.getInstance().showTacletView(app.taclet(),
                // true);
                break;
            }

        }

    }

    @Override
    protected JPanel init(TreeItem node, TreeItem r, JTree t, DefaultSMTSettings smtSettings) {

        int max = smtSettings != null ? smtSettings.getMaxNumberOfGenerics() : 0;
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
                genericLabel.setText("too many generic sorts: " + count);
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

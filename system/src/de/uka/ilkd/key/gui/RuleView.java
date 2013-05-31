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


package de.uka.ilkd.key.gui;

import java.awt.Component;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.util.Properties;

import javax.swing.BorderFactory;
import javax.swing.JScrollPane;
import javax.swing.JSplitPane;
import javax.swing.JTextArea;
import javax.swing.JTree;
import javax.swing.event.TreeSelectionEvent;
import javax.swing.event.TreeSelectionListener;
import javax.swing.tree.DefaultMutableTreeNode;
import javax.swing.tree.DefaultTreeCellRenderer;
import javax.swing.tree.TreeCellRenderer;

import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.pp.ProgramPrinter;
import de.uka.ilkd.key.proof.RuleTreeModel;
import de.uka.ilkd.key.rule.Rule;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.util.GuiUtilities;

public class RuleView extends JSplitPane implements TreeSelectionListener, java.io.Serializable {

    private static final String DESC_RESOURCE = "/de/uka/ilkd/key/gui/help/ruleExplanations.xml";
    private static final long serialVersionUID = 911181673407907024L;
    private RuleTreeModel ruleViewModel;
    private JTree ruleTree;
    private JTextArea contentPane;
    private JScrollPane contentScrollPane;
    private KeYMediator mediator;
    private Properties descriptions;

    /** Listener for proof changes */
    protected SelectionListener selectionListener = new SelectionListener();

    public RuleView() {
        super(VERTICAL_SPLIT);
        layoutPane();
        ruleTree.setCellRenderer(new RuleRenderer());
        ruleTree.addTreeSelectionListener(this);
        setVisible(true);
    }

    public void valueChanged(TreeSelectionEvent e) {
        if (ruleTree.getLastSelectedPathComponent() != null) {
            DefaultMutableTreeNode node = (DefaultMutableTreeNode) ruleTree
                    .getLastSelectedPathComponent();
            showTacletView(node);
        }
    }

    private void showTacletView(DefaultMutableTreeNode node) {

        Object userObj = node.getUserObject();
        String displayName;
        if (userObj instanceof Rule) {
            displayName = ((Rule) userObj).displayName();
        } else {
            displayName = userObj.toString();
        }

        contentScrollPane.setBorder(
                BorderFactory.createTitledBorder(displayName));

        if (userObj instanceof Taclet) {
            Taclet tac = (Taclet) userObj;
            contentPane.setText(toString(tac));
        } else {
            final int parenIdx = displayName.lastIndexOf("(");
            if (parenIdx >= 0) // strip number of taclets
                displayName = displayName.substring(0, parenIdx-1).intern();
            contentPane.setText(getRuleDescription(displayName));
        }

        contentPane.setCaretPosition(0);
    }

    private String getRuleDescription(String name) {
        String desc = getDescriptions().getProperty(name);
        if (desc == null) {
            return "No description available for " + name;
        } else {
            return desc;
        }
    }

    private String toString(Taclet tac) {
        LogicPrinter lp =
                new LogicPrinter(new ProgramPrinter(), new NotationInfo(), null, true);
        lp.printTaclet(tac);
        return lp.toString();
    }

    public void setMediator(KeYMediator p_mediator) {
        if (mediator != null) {
            unregisterAtMediator();
        }

        mediator = p_mediator;
        registerAtMediator();
        if (mediator != null && mediator.getSelectedProof() != null) {
            setRuleTreeModel(new RuleTreeModel(mediator.getSelectedGoal()));
        }
    }

    protected void setRuleTreeModel(RuleTreeModel model) {

        ruleViewModel = model;

        if (ruleViewModel != null) {
            ruleViewModel.updateTacletCount();
            ruleTree.setModel(ruleViewModel);
        }
    }

    protected void registerAtMediator() {
        mediator.addKeYSelectionListener(selectionListener);
    }

    protected void unregisterAtMediator() {
        mediator.removeKeYSelectionListener(selectionListener);
    }

    protected void layoutPane() {
        // initial placement of the divider
        setDividerLocation(300);

        // growing goes to the upper half only
        setResizeWeight(1.0);

        // this triggers storing the bar position
        setName("ruleViewPane");
        {
            ruleTree = new JTree(new String[] { "No proof loaded" });
            JScrollPane jp = new JScrollPane(ruleTree);
            setLeftComponent(jp);
        }
        {
            contentPane = new JTextArea("", 15, 30);
            contentPane.setEditable(false);
            contentPane.setLineWrap(true);
            contentPane.setWrapStyleWord(true);
            contentScrollPane = new JScrollPane(contentPane);
            setRightComponent(contentScrollPane);
        }

    }

    private class SelectionListener implements KeYSelectionListener {

        /** focused node has changed */
        public void selectedNodeChanged(KeYSelectionEvent e) {
            ruleViewModel.setSelectedGoal(e.getSource().getSelectedGoal());
        }

        /**
         * the selected proof has changed (e.g. a new proof has been loaded)
         */
        public void selectedProofChanged(KeYSelectionEvent e) {
            Runnable action = new Runnable() {
                public void run() {
                    if (mediator != null) {
                        if (mediator.getSelectedProof() != null) {
                            setRuleTreeModel(new RuleTreeModel(mediator.getSelectedGoal()));
                        } else {
                            ruleViewModel.setSelectedGoal(null);
                        }
                    }
                }
            };

            GuiUtilities.invokeOnEventQueue(action);
        }

    }

    private static class RuleRenderer extends DefaultTreeCellRenderer
            implements TreeCellRenderer, java.io.Serializable {

        private static final long serialVersionUID = 6129388673386459052L;

        public Component getTreeCellRendererComponent(JTree tree,
                Object value,
                boolean sel,
                boolean expanded,
                boolean leaf,
                int row,
                boolean hasFocus) {
            DefaultMutableTreeNode node = (DefaultMutableTreeNode) value;
            if (node.getUserObject() instanceof Taclet) {
                Taclet t = (Taclet) node.getUserObject();
                value = t.displayName();
            }

            Component comp = super.getTreeCellRendererComponent
                    (tree, value, sel, expanded, leaf, row, hasFocus);

            return comp;
        }
    }

    /**
     * This methods returns the map which contains descriptions for the elements
     * in the tree. The elements are read from the resource with the name
     * DESC_RESOURCE.
     * 
     * @return the descriptions read in from the config file
     */
    public Properties getDescriptions() {
        if (descriptions == null) {
            descriptions = new Properties();
            InputStream is = getClass().getResourceAsStream(DESC_RESOURCE);
            try {
                if (is == null) {
                    throw new FileNotFoundException(DESC_RESOURCE + " not found");
                }
                descriptions.loadFromXML(is);
            } catch (IOException e) {
                System.err.println("Cannot not load help messages in rule view");
                e.printStackTrace();
            }
        }
        return descriptions;
    }

}

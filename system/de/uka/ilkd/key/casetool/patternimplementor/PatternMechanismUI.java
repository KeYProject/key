// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.casetool.patternimplementor;

import java.awt.BorderLayout;
import java.awt.Dimension;
import java.awt.FlowLayout;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.util.Enumeration;
import java.util.Observable;
import java.util.Observer;

import javax.swing.*;
import javax.swing.tree.DefaultMutableTreeNode;
import javax.swing.tree.TreePath;

public class PatternMechanismUI implements ActionListener, Observer {

    private static final String OK = "Ok";

    private static final String PREVIEW = "Preview";

    private static final String CANCEL = "Cancel";

    PatternMechanism pm;

    // the main window, all parts except buttonPanel should be in scrollpanes
    JDialog mainDialog;

    // the ui of the pattern
    JPanel patternPanel;

    // a tree where it's possible to select which pattern to use
    JTree patternSelectorTree;

    // apply, cancel, preview
    JPanel buttonPanel;

    // the buttons in the buttonPanel
    JButton okButton;

    JButton previewButton;

    JButton cancelButton;

    // shows information about the pattern
    JComponent infoPanel;

    public PatternMechanismUI(PatternMechanism pm) {
        setPatternMechanism(pm);
        buildUI();
    }

    public void setPatternMechanism(PatternMechanism pm) {
        this.pm = pm;
        pm.addObserver(this);
    }

    private void buildUI() {
        //System.out.println("buildUI");
        if (mainDialog == null) {
            patternSelectorTree = buildTree();

            buttonPanel = new JPanel();
            buttonPanel.setLayout(new FlowLayout());

            okButton = new JButton(OK);
            previewButton = new JButton(PREVIEW);
            cancelButton = new JButton(CANCEL);
            okButton.addActionListener(this);
            previewButton.addActionListener(this);
            cancelButton.addActionListener(this);

            buttonPanel.add(previewButton);
            buttonPanel.add(okButton);
            buttonPanel.add(cancelButton);

            mainDialog = new JDialog(new JFrame(), "KeY Pattern Mechanism",
                    true);

            mainDialog.setSize(new Dimension(700, 500));

            /*
             * mainWindowDialog = new JDialog(new JFrame(), true);
             * mainWindowDialog.getContentPane().add(mainFrame);
             * mainWindowDialog.setVisible(true);
             */
        }

        mainDialog.getContentPane().removeAll();
        mainDialog.getContentPane().setLayout(new BorderLayout());
        mainDialog.getContentPane().add(new JScrollPane(patternSelectorTree),
                BorderLayout.WEST);
        mainDialog.getContentPane().add(buttonPanel, BorderLayout.SOUTH);

        mainDialog.getContentPane().add(new JScrollPane(centerPanel()),
                BorderLayout.CENTER);

        //mainFrame.pack();
        mainDialog.setVisible(true);
    }

    public void update(Observable o, Object arg) {
        //System.out.println("PMUI.update");
        buildUI();
    }

    private JPanel centerPanel() {
        JPanel center = new JPanel();

        try {
            patternPanel = new PIParameterGUIGroup(pm.getParameters());
            center.setLayout(new BorderLayout());
            center.add(patternPanel, BorderLayout.WEST);
            infoPanel = new JTextArea(pm.getImplementation().toString());
            ((JTextArea) infoPanel).setEditable(false);
            center.add(infoPanel, BorderLayout.SOUTH);
        } catch (Exception e) {
            e.printStackTrace();

            JLabel label = new JLabel("No Patterns found");
            center.add(label);
        }

        return center;
    }

    /**
     * /-------------------------\ | pS-tree | patternPanel | | | | | | | |
     * +---------------| | | infoPanel | | | | |-------------------------| |
     * buttonPanel | | [Preview][Ok][Cancel] | \-------------------------/
     */
    public void actionPerformed(ActionEvent e) {
        if (OK.equals(e.getActionCommand())) {
            //System.out.println("Button pressed: " + OK);
            //System.out.println(pm.getImplementation());
	    PIParameterGroup pg = pm.getParameters();
	    String[] constraint = new String[pg.size()];
	    for (int i=0; i<constraint.length; i++) {
		constraint[i] = pg.getValue(i);
		//System.out.println("constraint[" + i + "] = " + constraint[i]);
	    }
            mainDialog.dispose();

            //pm.setPattern(pm.getPatterns()[1]);
        } else if (PREVIEW.equals(e.getActionCommand())) {
            //System.out.println("Button pressed: " + PREVIEW);

            //infoPanel.setVisible(false);
            ((JTextArea) infoPanel).setText(pm.getImplementation().toString());

            //((JTextArea)infoPanel).setEditable(false);
            //infoPanel.setVisible(true);
        } else if (CANCEL.equals(e.getActionCommand())) {
            //System.out.println("Button pressed: " + CANCEL);
            //System.out.println("Remove this exit feature");
            //System.exit(0);
            this.pm.cancel();
            mainDialog.dispose();
        }
    }

    private JTree buildTree() {
        //pm.getPatterns();
        DefaultMutableTreeNode root = new DefaultMutableTreeNode("Design patterns");

        //DefaultMutableTreeNode selected;
        TreePath actualPath = new TreePath(root);

        for (int i = 0; i < pm.getPatterns().length; i++) {
            PMTreeNode node = new PMTreeNode(pm.getPatterns()[i]);

            //node.addTreeSelectionListener(pm);
            String path = node.getpmPath();
            DefaultMutableTreeNode lastNode = root;

            while (path.indexOf(':') != -1) {
                //System.out.println("path " + path);
                DefaultMutableTreeNode tmpnode = new DefaultMutableTreeNode(
                        path.substring(0, path.indexOf(':')));
                path = path.substring(path.indexOf(':') + 1, path.length());

                /*
                 * System.err.println("lastNode.getIndex(tmpnode) = " +
                 * lastNode.getIndex(tmpnode));
                 */
                for (Enumeration e = lastNode.children(); e.hasMoreElements();) {
                    DefaultMutableTreeNode child = (DefaultMutableTreeNode) e
                            .nextElement();

                    if (child.toString().equals(tmpnode.toString())) {
                        tmpnode = child;
                    }
                }

                lastNode.add(tmpnode);
                lastNode = tmpnode;

                if (i == 0) {
                    actualPath = actualPath.pathByAddingChild(lastNode);
                }
            }

            lastNode.add(node);

            if (i == 0) {
                actualPath = actualPath.pathByAddingChild(node);
            }
        }

        JTree tree = new JTree(root);
        tree.setVisible(false);

        //System.out.println(actualPath);
        //System.out.println("trying to set the path");
        //System.out.println("old : " + tree.getSelectionPath());
        tree.setSelectionPath(actualPath);

        //System.out.println("new : " + tree.getSelectionPath());
        tree.setExpandsSelectedPaths(true);

        tree.setRootVisible(true);
        tree.setVisible(true);

        tree.addTreeSelectionListener(pm);

        return tree;
    }
}

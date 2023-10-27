/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.settings;

import java.awt.*;
import java.awt.event.KeyAdapter;
import java.awt.event.KeyEvent;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Enumeration;
import java.util.LinkedList;
import java.util.List;
import java.util.stream.Collectors;
import javax.swing.*;
import javax.swing.tree.DefaultTreeCellRenderer;
import javax.swing.tree.DefaultTreeModel;
import javax.swing.tree.TreeNode;
import javax.swing.tree.TreePath;

import de.uka.ilkd.key.gui.MainWindow;

/**
 * @author Alexander Weigl
 * @version 1 (08.04.19)
 */
public class SettingsUi extends JPanel {
    private static final long serialVersionUID = -217841876110516940L;
    private static int calculatedWidth = 0;

    private final JSplitPane root;
    private final JComponent westPanel;
    private DefaultTreeModel treeModel = new DefaultTreeModel(null, false);
    private final JTree treeSettingsPanels = new JTree(treeModel);
    private final JTextField txtSearch = new JTextField();
    private final MainWindow mainWindow;
    private final JDialog frame;

    public SettingsUi(MainWindow mainWindow, JDialog frame) {
        this.frame = frame;
        this.mainWindow = mainWindow;
        treeSettingsPanels.setBorder(BorderFactory.createEmptyBorder(5, 5, 5, 5));
        // TODO: scale this with the global font factor too
        treeSettingsPanels.setFont(treeSettingsPanels.getFont().deriveFont(16.0f));
        treeSettingsPanels.setCellRenderer(new DefaultTreeCellRenderer() {
            private static final long serialVersionUID = 1770380144400699946L;

            @Override
            public Component getTreeCellRendererComponent(JTree tree, Object value, boolean sel,
                    boolean expanded, boolean leaf, int row, boolean hasFocus) {
                SettingsTreeNode node = (SettingsTreeNode) value;
                SettingsProvider panel = node.provider;
                JLabel lbl;
                if (panel == null) {
                    // root entry
                    lbl = (JLabel) super.getTreeCellRendererComponent(tree, "KeY Settings", sel,
                        expanded, leaf, row, hasFocus);
                } else {
                    lbl = (JLabel) super.getTreeCellRendererComponent(tree, panel.getDescription(),
                        sel, expanded, leaf, row, hasFocus);

                    if (node.isLeaf()) {
                        lbl.setIcon(panel.getIcon());
                    }
                    lbl.setBorder(BorderFactory.createEmptyBorder(2, 2, 2, 2));
                    if (!txtSearch.getText().isEmpty() && panel.contains(txtSearch.getText())) {
                        lbl.setBackground(Color.black);
                        lbl.setBorder(BorderFactory.createLineBorder(Color.BLUE, 2, true));
                    } else {
                        lbl.setBackground(Color.white);
                        lbl.setBorder(null);
                    }
                }
                return lbl;
            }
        });

        txtSearch.addKeyListener(new KeyAdapter() {
            @Override
            public void keyReleased(KeyEvent e) {
                treeSettingsPanels.invalidate();
                treeSettingsPanels.repaint();
            }
        });

        root = new JSplitPane();
        // root.setRightComponent(center = new JScrollPane());
        treeSettingsPanels.addTreeSelectionListener(e -> {
            SettingsTreeNode n = (SettingsTreeNode) e.getPath().getLastPathComponent();
            if (n.provider != null && n.provider.getPanel(mainWindow) != null) {
                JComponent comp = n.provider.getPanel(mainWindow);
                // center.setViewportView(comp);
                // center.getVerticalScrollBar().setValue(0);
                // center.setHorizontalScrollBarPolicy(JScrollPane.HORIZONTAL_SCROLLBAR_NEVER);
                // comp.setSize(center.getWidth(), comp.getHeight());
                // comp.setPreferredSize(new Dimension(center.getWidth(), comp.getHeight()));
                setSettingsPanel(comp);
            }
        });

        setLayout(new BorderLayout(5, 5));
        westPanel = createWestPanel();
        root.setLeftComponent(westPanel);
        root.setRightComponent(new JLabel("empty"));
        add(root, BorderLayout.CENTER);
        root.setDividerLocation(0.3d);
    }

    private void setSettingsPanel(JComponent comp) {
        SwingUtilities.updateComponentTreeUI(comp);
        root.setRightComponent(comp);

        // set divider location slightly more to the right to avoid horizontal scroll bar
        root.setDividerLocation(root.getLeftComponent().getPreferredSize().width + 2);
    }

    private JPanel createWestPanel() {
        JPanel p = new JPanel(new BorderLayout(5, 5));
        Box boxNorth = new Box(BoxLayout.X_AXIS);
        JLabel lblSearch;
        boxNorth.add(lblSearch = new JLabel("Search: "));
        boxNorth.add(txtSearch);
        lblSearch.setLabelFor(txtSearch);
        p.add(boxNorth, BorderLayout.NORTH);
        p.add(new JScrollPane(treeSettingsPanels));
        p.setBorder(BorderFactory.createEmptyBorder(5, 5, 5, 5));
        return p;
    }

    /**
     * Configure the settings providers to display. Calculates the maximum width of the settings UI.
     *
     * @param providers settings providers
     * @return maximum width of the dialog
     */
    public int setSettingsProvider(List<SettingsProvider> providers) {
        SettingsTreeNode root = new SettingsTreeNode(providers);
        treeModel = new DefaultTreeModel(root);
        treeSettingsPanels.setModel(treeModel);
        LinkedList<TreePath> list = new LinkedList<>();
        getPaths(new TreePath(treeModel.getPathToRoot(root)), list);
        list.forEach(treeSettingsPanels::expandPath);

        if (!providers.isEmpty()) {
            setSettingsPanel(providers.get(0).getPanel(mainWindow));
        }
        // determine optimal dialog width
        if (calculatedWidth != 0) {
            return calculatedWidth;
        }
        int w = providers.stream().flatMap(x -> {
            // collect all children providers
            List<SettingsProvider> all = new ArrayList<>();
            List<SettingsProvider> q = List.of(x);
            while (!q.isEmpty()) {
                List<SettingsProvider> newQ = new ArrayList<>();
                for (var provider : q) {
                    all.add(provider);
                    newQ.addAll(provider.getChildren());
                }
                q = newQ;
            }
            return all.stream();
        }).map(x -> {
            JPanel panel = (JPanel) x.getPanel(mainWindow);
            setSettingsPanel(panel);
            frame.pack();
            return panel.getWidth();
        }).max(Integer::compareTo).orElse(600);
        setSettingsPanel(!providers.isEmpty() ? providers.get(0).getPanel(mainWindow) : null);
        calculatedWidth = w + westPanel.getWidth() + this.root.getDividerSize() + 30;
        return calculatedWidth;
    }

    public void getPaths(TreePath parent, List<TreePath> list) {
        list.add(parent);

        TreeNode node = (TreeNode) parent.getLastPathComponent();
        if (node.getChildCount() >= 0) {
            for (Enumeration<? extends TreeNode> e = node.children(); e.hasMoreElements();) {
                TreeNode n = e.nextElement();
                TreePath path = parent.pathByAddingChild(n);
                getPaths(path, list);
            }
        }
    }

    public void selectPanel(SettingsProvider provider) {
        SettingsTreeNode node = findNode(provider);
        TreePath path = new TreePath(treeModel.getPathToRoot(node));
        treeSettingsPanels.setSelectionPath(path);
    }

    SettingsTreeNode findNode(SettingsProvider provider) {
        LinkedList<SettingsTreeNode> nodes = new LinkedList<>();
        nodes.offer((SettingsTreeNode) treeModel.getRoot());
        while (!nodes.isEmpty()) {
            SettingsTreeNode cur = nodes.poll();
            if (cur.provider == provider) {
                return cur;
            }
            nodes.addAll(cur.children);
        }
        return null;
    }
}


class SettingsTreeNode implements TreeNode {
    final SettingsProvider provider;
    final List<SettingsTreeNode> children;

    SettingsTreeNode(SettingsProvider cur, List<SettingsProvider> providers) {
        provider = cur;
        if (!providers.isEmpty()) {
            children = providers.stream().map(SettingsTreeNode::new).collect(Collectors.toList());
        } else {
            children = Collections.emptyList();
        }
    }

    public SettingsTreeNode(List<SettingsProvider> providers) {
        this(null, providers);
    }

    public SettingsTreeNode(SettingsProvider provider) {
        this(provider, provider.getChildren());
    }

    @Override
    public TreeNode getChildAt(int childIndex) {
        return children.get(childIndex);
    }

    @Override
    public int getChildCount() {
        return children.size();
    }

    @Override
    public TreeNode getParent() {
        return null;
    }

    @Override
    public int getIndex(TreeNode node) {
        return children.indexOf(node);
    }

    @Override
    public boolean getAllowsChildren() {
        return children.size() != 0;
    }

    @Override
    public boolean isLeaf() {
        return children.isEmpty();
    }

    @Override
    public Enumeration<? extends TreeNode> children() {
        return Collections.enumeration(children);
    }
}

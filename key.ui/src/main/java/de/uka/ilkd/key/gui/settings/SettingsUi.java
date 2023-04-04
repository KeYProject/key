package de.uka.ilkd.key.gui.settings;

import java.awt.*;
import java.awt.event.KeyAdapter;
import java.awt.event.KeyEvent;
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
import de.uka.ilkd.key.gui.fonticons.IconFactory;

/**
 * @author Alexander Weigl
 * @version 1 (08.04.19)
 */
public class SettingsUi extends JPanel {
    private static final long serialVersionUID = -217841876110516940L;
    private static final Icon ICON_TREE_NODE_RETRACTED = IconFactory.TREE_NODE_EXPANDED.get();
    private static final Icon ICON_TREE_NODE_EXPANDED = IconFactory.TREE_NODE_RETRACTED.get();

    private final JSplitPane root;
    private DefaultTreeModel treeModel = new DefaultTreeModel(null, false);
    private final JTree treeSettingsPanels = new JTree(treeModel);
    private final JTextField txtSearch = new JTextField();
    private final MainWindow mainWindow;
    // private JScrollPane center;

    public SettingsUi(MainWindow mainWindow) {
        this.mainWindow = mainWindow;
        treeSettingsPanels.setBorder(BorderFactory.createEmptyBorder(5, 5, 5, 5));
        treeSettingsPanels.setCellRenderer(new DefaultTreeCellRenderer() {
            private static final long serialVersionUID = 1770380144400699946L;

            @Override
            public Component getTreeCellRendererComponent(JTree tree, Object value, boolean sel,
                    boolean expanded, boolean leaf, int row, boolean hasFocus) {
                SettingsTreeNode node = (SettingsTreeNode) value;
                SettingsProvider panel = node.provider;
                JLabel lbl;
                if (panel == null) {
                    lbl = (JLabel) super.getTreeCellRendererComponent(tree, value, sel, expanded,
                        leaf, row, hasFocus);
                } else {
                    lbl = (JLabel) super.getTreeCellRendererComponent(tree, panel.getDescription(),
                        sel, expanded, leaf, row, hasFocus);
                    lbl.setFont(lbl.getFont().deriveFont(16f));

                    if (!node.isLeaf()) {
                        lbl.setIcon(expanded ? ICON_TREE_NODE_EXPANDED : ICON_TREE_NODE_RETRACTED);
                    } else {
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

        treeSettingsPanels.setRootVisible(false);
        setLayout(new BorderLayout(5, 5));
        root.setLeftComponent(createWestPanel());
        root.setRightComponent(new JLabel("empty"));
        add(root, BorderLayout.CENTER);
        root.setDividerLocation(0.3d);
    }

    private void setSettingsPanel(JComponent comp) {
        // int dividerLocation = root.getDividerLocation();
        root.setRightComponent(comp);
        // root.setDividerLocation(dividerLocation);

        root.setDividerLocation(root.getLeftComponent().getPreferredSize().width);
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

    public void setSettingsProvider(List<SettingsProvider> providers) {
        SettingsTreeNode root = new SettingsTreeNode(providers);
        treeModel = new DefaultTreeModel(root);
        treeSettingsPanels.setModel(treeModel);
        LinkedList<TreePath> list = new LinkedList<>();
        getPaths(new TreePath(treeModel.getPathToRoot(root)), list);
        list.forEach(treeSettingsPanels::expandPath);

        if (!providers.isEmpty()) {
            setSettingsPanel(providers.get(0).getPanel(mainWindow));
        }
    }

    public void getPaths(TreePath parent, List<TreePath> list) {
        list.add(parent);

        TreeNode node = (TreeNode) parent.getLastPathComponent();
        if (node.getChildCount() >= 0) {
            for (Enumeration e = node.children(); e.hasMoreElements();) {
                TreeNode n = (TreeNode) e.nextElement();
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

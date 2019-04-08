package de.uka.ilkd.key.gui.settings;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.smt.OptionContentNode;

import javax.swing.*;
import javax.swing.tree.*;
import java.awt.*;
import java.util.Collections;
import java.util.Enumeration;
import java.util.LinkedList;
import java.util.List;
import java.util.stream.Collectors;

/**
 * @author Alexander Weigl
 * @version 1 (08.04.19)
 */
public class SettingsUi extends JPanel {
    private DefaultTreeModel treeModel = new DefaultTreeModel(null, false);
    private JTree treeSettingsPanels = new JTree(treeModel);
    private JTextField txtSearch = new JTextField();


    public SettingsUi(MainWindow mainWindow) {
        treeSettingsPanels.setCellRenderer(new DefaultTreeCellRenderer() {
            @Override
            public Component getTreeCellRendererComponent(JTree tree, Object value, boolean sel, boolean expanded, boolean leaf, int row, boolean hasFocus) {
                SettingsTreeNode node = (SettingsTreeNode) value;
                SettingsProvider panel = node.provider;
                if (panel == null) {
                    return super.getTreeCellRendererComponent(tree, value, sel, expanded, leaf, row, hasFocus);
                } else {
                    JLabel lbl = (JLabel) super.getTreeCellRendererComponent(tree, panel.getDescription(), sel, expanded, leaf, row, hasFocus);
                    lbl.setIcon(panel.getIcon());
                    lbl.setFont(lbl.getFont().deriveFont(16f));
                    return lbl;
                }
            }
        });

        JSplitPane root = new JSplitPane();

        treeSettingsPanels.addTreeSelectionListener(e -> {
            SettingsTreeNode n = (SettingsTreeNode) e.getPath().getLastPathComponent();
            if (n.provider != null && n.provider.getPanel(mainWindow) != null) {
                root.setRightComponent(n.provider.getPanel(mainWindow));
            }

        });

        treeSettingsPanels.setRootVisible(false);
        setLayout(new BorderLayout(5, 5));
        JScrollPane spCenter = new JScrollPane();
        root.setLeftComponent(createWestPanel());
        root.setRightComponent(spCenter);
        add(root, BorderLayout.CENTER);
    }

    private JPanel createWestPanel() {
        JPanel p = new JPanel(new BorderLayout(5,5));
        Box boxNorth = new Box(BoxLayout.X_AXIS);
        JLabel lblSearch;
        boxNorth.add(lblSearch = new JLabel("Search"));
        boxNorth.add(txtSearch);
        lblSearch.setLabelFor(txtSearch);
        p.add(boxNorth, BorderLayout.NORTH);
        p.add(new JScrollPane(treeSettingsPanels));
        return p;
    }

    public void setSettingsProvider(List<SettingsProvider> providers) {
        treeModel = new DefaultTreeModel(new SettingsTreeNode(providers));
        treeSettingsPanels.setModel(treeModel);
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
            children = providers.stream().map(SettingsTreeNode::new)
                    .collect(Collectors.toList());
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

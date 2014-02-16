package de.uka.ilkd.key.gui;

import de.uka.ilkd.key.rule.Taclet;
import java.awt.Component;
import javax.swing.JTree;
import javax.swing.tree.DefaultMutableTreeNode;
import javax.swing.tree.DefaultTreeCellRenderer;
import javax.swing.tree.DefaultTreeModel;

/**
 * This class is used by {@link InfoView} to display the description contents as
 * a tree.
 *
 * @author Kai Wallisch <kai.wallisch@ira.uka.de>
 */
public class InfoTree extends JTree {

    private static final String DESC_RESOURCE = "/de/uka/ilkd/key/gui/help/ruleExplanations.xml";
    private final XMLProperties ruleExplanations;

    InfoTree() {
        ruleExplanations = new XMLProperties(DESC_RESOURCE);
        setModel(new DefaultTreeModel(new InfoTreeNode("No proof loaded", ruleExplanations)));

        setCellRenderer(new DefaultTreeCellRenderer() {
            @Override
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
                Component comp = super.getTreeCellRendererComponent(tree, value, sel, expanded, leaf, row, hasFocus);
                return comp;
            }
        });
    }

    @Override
    public InfoTreeNode getLastSelectedPathComponent() {
        return (InfoTreeNode) super.getLastSelectedPathComponent();
    }

}

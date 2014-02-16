package de.uka.ilkd.key.gui;

import de.uka.ilkd.key.rule.Taclet;
import java.awt.Component;
import javax.swing.JTree;
import javax.swing.tree.DefaultMutableTreeNode;
import javax.swing.tree.DefaultTreeCellRenderer;

/**
 * This class is used by {@link InfoView} to display the description contents as
 * a tree.
 *
 * @author Kai Wallisch <kai.wallisch@ira.uka.de>
 */
public class InfoTree extends JTree {

    InfoTree() {
        super(new InfoTreeNode("No proof loaded"));

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

package de.uka.ilkd.key.gui;

import javax.swing.JTree;
import javax.swing.tree.DefaultMutableTreeNode;
import javax.swing.tree.DefaultTreeModel;

/**
 * This class is used by {@link InfoView} to display its contents.
 *
 * @author Kai Wallisch <kai.wallisch@ira.uka.de>
 */
public class InfoTree extends JTree {

    /**
     *
     */
    private static final long serialVersionUID = 2018185104131516569L;

    InfoTree() {
        DefaultMutableTreeNode root = new DefaultMutableTreeNode();
        root.add(new InfoTreeNode("No proof loaded",
                "In this pane, the available logical rules will be displayed and/or explained."));
        setModel(new DefaultTreeModel(root));
        setShowsRootHandles(true);
        setRootVisible(false);
    }

    /*
     * This function is expected to return only {@link InfoTreeNode} instances.
     * The super method returns {@link DefaultMutableTreeNode} instances.
     */
    @Override
    public InfoTreeNode getLastSelectedPathComponent() {
        return (InfoTreeNode) super.getLastSelectedPathComponent();
    }

}

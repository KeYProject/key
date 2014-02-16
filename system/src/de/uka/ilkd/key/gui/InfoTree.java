package de.uka.ilkd.key.gui;

import javax.swing.JTree;
import javax.swing.tree.DefaultMutableTreeNode;
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
        DefaultMutableTreeNode root = new DefaultMutableTreeNode();
        root.add(new InfoTreeNode("No proof loaded", ruleExplanations));
        setModel(new DefaultTreeModel(root));
        setShowsRootHandles(true);
        setRootVisible(false);
    }

    @Override
    public InfoTreeNode getLastSelectedPathComponent() {
        return (InfoTreeNode) super.getLastSelectedPathComponent();
    }

}

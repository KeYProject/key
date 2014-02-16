package de.uka.ilkd.key.gui;

import javax.swing.JTree;

/**
 * This class is used by {@link InfoView} to display the description contents
 * as a tree.
 * 
 * @author Kai Wallisch <kai.wallisch@ira.uka.de>
 */
public class InfoTree extends JTree {

    InfoTree() {
        super(new InfoTreeNode("No proof loaded"));
    }

    @Override
    public InfoTreeNode getLastSelectedPathComponent() {
        return (InfoTreeNode) super.getLastSelectedPathComponent();
    }

}

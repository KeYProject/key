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
    }

    @Override
    public InfoTreeNode getLastSelectedPathComponent() {
        return (InfoTreeNode) super.getLastSelectedPathComponent();
    }

}

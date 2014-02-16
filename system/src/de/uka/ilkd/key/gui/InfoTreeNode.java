package de.uka.ilkd.key.gui;

import javax.swing.tree.DefaultMutableTreeNode;

/**
 * Instances of this class are nodes of {@link InfoTree}.
 *
 * @author Kai Wallisch <kai.wallisch@ira.uka.de>
 */
public class InfoTreeNode extends DefaultMutableTreeNode {

    InfoTreeNode(String title) {
        super(title);
    }

}

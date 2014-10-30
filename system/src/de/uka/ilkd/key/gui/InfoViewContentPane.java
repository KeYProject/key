package de.uka.ilkd.key.gui;

import javax.swing.BorderFactory;
import javax.swing.JScrollPane;
import javax.swing.JTextArea;

/**
 * This class is used to display descriptions in {@link InfoView}.
 *
 * @author Kai Wallisch <kai.wallisch@ira.uka.de>
 */
public class InfoViewContentPane extends JScrollPane {

    /**
     *
     */
    private static final long serialVersionUID = -7609483136106706196L;
    private final JTextArea description;

    InfoViewContentPane() {
        description = new JTextArea("", 15, 30);
        description.setEditable(false);
        description.setLineWrap(true);
        description.setWrapStyleWord(true);
        setViewportView(description);
    }

    public void setNode(InfoTreeNode node) {
        setBorder(BorderFactory.createTitledBorder(node.getTitle()));
        description.setText(node.getDescription());
        description.setCaretPosition(0);
    }

}

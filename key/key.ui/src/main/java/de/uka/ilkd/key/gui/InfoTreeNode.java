package de.uka.ilkd.key.gui;

import java.util.Properties;

import javax.swing.tree.DefaultMutableTreeNode;

import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.pp.ProgramPrinter;
import de.uka.ilkd.key.rule.Taclet;

/**
 * Every node of {@link InfoTree} is an instance of this class.
 *
 * @author Kai Wallisch <kai.wallisch@ira.uka.de>
 */
public class InfoTreeNode extends DefaultMutableTreeNode {

	private static final long serialVersionUID = 4187650510339169399L;
	// the original taclet name
    private final String altName;
    private final String description;

    /*
     * This constructor should only be used for the invisible root node of
     * {@link InfoTreeModel}.
     */
    InfoTreeNode() {
        super("root node");
        altName = null;
        description = "This is the root node of InfoTreeModel. It should not be visible.";
    }

    /*
     * @param title The name of the node.
     * @param explanations An XML resource containing node descriptions.
     */
    InfoTreeNode(String title, Properties explanations) {
        super(title);

        altName = null;
        String desc = explanations.getProperty(title);

        if (desc == null) {
            description = "No description available for " + title + ".";
        } else {
            description = desc;
        }

    }

    InfoTreeNode(Taclet taclet) {
        super(taclet.displayName());
        altName = taclet.name().toString();
        LogicPrinter lp = new LogicPrinter(new ProgramPrinter(), new NotationInfo(), null, true);
        lp.printTaclet(taclet);
        description = lp.toString();
    }

    InfoTreeNode(String title, String description) {
        super(title);
        altName = null;
        this.description = description;
    }

    String getTitle() {
        return (String) getUserObject();
    }
    
    /**
     * switch title to alternative name (i.e., internal taclet name)
     */
    void setTitleToAltName() {
    	assert altName != null;
    	userObject = altName;
    }

    String getDescription() {
        return description;
    }

}

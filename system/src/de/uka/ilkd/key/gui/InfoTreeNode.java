package de.uka.ilkd.key.gui;

import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.pp.ProgramPrinter;
import de.uka.ilkd.key.rule.Taclet;
import javax.swing.tree.DefaultMutableTreeNode;

/**
 * Instances of this class are nodes of {@link InfoTree}.
 *
 * @author Kai Wallisch <kai.wallisch@ira.uka.de>
 */
public class InfoTreeNode extends DefaultMutableTreeNode {

    final Description description;

    /*
     * This constructor should only be used for the invisible root node of
     * {@link InfoTreeModel}.
     */
    InfoTreeNode() {
        super("root node");
        description = new Description() {
            @Override
            public String getString() {
                return "This is the root node of InfoTreeModel. It should not be visible.";
            }
        };
    }

    /*
     * @param title The name of the node.
     * @param explanations The XML resource, where the description for this node comes from.
     */
    InfoTreeNode(final String title, final XMLProperties explanations) {
        super(title);
        description = new Description() {
            @Override
            public String getString() {
                int parenIdx = title.lastIndexOf("(");
                String shortenedTitle;
                if (parenIdx >= 0) // strip number of taclets
                {
                    shortenedTitle = title.substring(0, parenIdx - 1).intern();
                } else {
                    shortenedTitle = title;
                }
                String desc = explanations.getProperty(shortenedTitle);

                if (desc == null) {
                    return "No description available for " + shortenedTitle + ".";
                } else {
                    return desc;
                }
            }
        };
    }

    InfoTreeNode(final Taclet taclet) {
        super(taclet.displayName());
        description = new Description() {
            @Override
            public String getString() {
                LogicPrinter lp = new LogicPrinter(new ProgramPrinter(), new NotationInfo(), null, true);
                lp.printTaclet(taclet);
                return lp.toString();
            }
        };
    }

    InfoTreeNode(String title, final String description) {
        super(title);
        this.description = new Description() {
            @Override
            public String getString() {
                return description;
            }
        };
    }

    String getTitle() {
        return (String) getUserObject();
    }

    String getDescription() {
        return description.getString();
    }

    private static interface Description {

        String getString();
    }

}

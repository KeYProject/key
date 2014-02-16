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

    final String title;
    final Object description;

    InfoTreeNode(final String title, final XMLProperties explanations) {
        super(title);
        this.title = title;
        description = new Object() {
            @Override
            public String toString() {
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
        title = taclet.displayName();
        description = new Object() {
            @Override
            public String toString() {
                LogicPrinter lp = new LogicPrinter(new ProgramPrinter(), new NotationInfo(), null, true);
                lp.printTaclet(taclet);
                return lp.toString();
            }
        };
    }

    String getTitle() {
        return title;
    }

    String getDescription() {
        return description.toString();
    }

}

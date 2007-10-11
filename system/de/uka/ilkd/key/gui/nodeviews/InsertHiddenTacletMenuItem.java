package de.uka.ilkd.key.gui.nodeviews;

import javax.swing.JFrame;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.rule.ListOfTacletGoalTemplate;
import de.uka.ilkd.key.rule.NoFindTaclet;
import de.uka.ilkd.key.rule.Taclet;

/**
 * This item groups all insert hidden taclets and offers a
 * more convienient user interface to add them.
 *
 */
public class InsertHiddenTacletMenuItem extends InsertionTacletBrowserMenuItem {
    
   
    /**
     * creates an instance of the insert hidden menu item
     * @param parent the JFrame with the parent frame
     * @param notInfo the NotationInfo to be used for pretty printing 
     * the apps
     * @param services the Services
     */
    public InsertHiddenTacletMenuItem(JFrame parent, 
            NotationInfo notInfo, Services services) {
        super("Insert Hidden", parent, notInfo, services);  
    }
 
    /**
     * determines the sequent with the formulas to be added
     * or null if the given taclet is not thought to be displayed 
     * by this component
     * @param t the Taclet
     * @return the sequent with the formulas to be added
     * or null
     */
    protected Sequent checkTaclet(Taclet t) {
        if (!(t instanceof NoFindTaclet) || 
                !t.displayName().startsWith("insert_hidden")) {
            return null;
        }
        
        final ListOfTacletGoalTemplate goalTemplates = t.goalTemplates(); 
        if (goalTemplates.size() != 1) return null;
        return goalTemplates.head().sequent();
    }
}

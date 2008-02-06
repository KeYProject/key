package de.uka.ilkd.key.gui.nodeviews;

import java.util.Collection;
import java.util.Comparator;
import java.util.TreeSet;

import javax.swing.JFrame;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.rule.ListOfTacletGoalTemplate;
import de.uka.ilkd.key.rule.NoFindTaclet;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApp;

/**
 * This menu item groups all taclets which allow to insert class invariants 
 */
public class InsertSystemInvariantTacletMenuItem extends InsertionTacletBrowserMenuItem {
   
    /**
     * creates an instance of the insert hidden menu item
     * @param parent the JFrame with the parent frame
     * @param notInfo the NotationInfo to be used for pretty printing 
     * the apps
     * @param services the Services
     */
    public InsertSystemInvariantTacletMenuItem(JFrame parent, 
            NotationInfo notInfo, Services services) {
        super("Insert Class Invariant", parent, notInfo, services);        
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
                !t.displayName().startsWith("Insert implicit invariants of")) {
            return null;
        }
        
        final ListOfTacletGoalTemplate goalTemplates = t.goalTemplates(); 
        if (goalTemplates.size() != 1) return null;
        return goalTemplates.head().sequent();
    }
    
    /**
     * show the taclets sorted  
     */
    protected Collection createInsertionList() {
        return new TreeSet(new Lexicographical());
    }
    
    
    public TacletAppListItem createListItem(TacletApp app) {
        return new ClassInvAppItem(app, checkTaclet(app.taclet()), 
                notInfo, services);
    }
    
    final static class Lexicographical implements Comparator {
        public int compare(Object arg0, Object arg1) {
        
            return ((TacletAppListItem)arg0).shortDescription().
                compareTo(((TacletAppListItem)arg1).shortDescription());
        }
    }

    /**
     * inner class to pretty print the formulas to be added
     */
    static class ClassInvAppItem extends TacletAppListItem {
       
        public ClassInvAppItem(TacletApp app, Sequent seq, NotationInfo notInfo, 
                Services services) {
            super(app, seq, notInfo, services);
        }
              
        public String shortDescription() {
            final String displayName = getTacletApp().taclet().displayName();
            return displayName.replaceFirst("Insert invariants of ", "");
        }      
        
        public String toString() {
            return shortDescription();
        }
    }
 

}

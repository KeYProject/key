// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.gui.nodeviews;

import java.util.Collection;
import java.util.Comparator;
import java.util.TreeSet;

import javax.swing.JFrame;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.rule.NoFindTaclet;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.tacletbuilder.TacletGoalTemplate;

/**
 * This menu item groups all taclets which allow to insert class invariants 
 */
public class InsertSystemInvariantTacletMenuItem extends InsertionTacletBrowserMenuItem {
   
    /**
     * 
     */
    private static final long serialVersionUID = -4303059934911952345L;

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
        
        final ImmutableList<TacletGoalTemplate> goalTemplates = t.goalTemplates(); 
        if (goalTemplates.size() != 1) return null;
        return goalTemplates.head().sequent();
    }
    
    /**
     * show the taclets sorted  
     */
    protected Collection<TacletAppListItem> createInsertionList() {
        return new TreeSet<TacletAppListItem>(new Lexicographical());
    }
    
    
    public TacletAppListItem createListItem(TacletApp app) {
        return new ClassInvAppItem(app, checkTaclet(app.taclet()), 
                notInfo, services);
    }
    
    final static class Lexicographical implements Comparator<TacletAppListItem> {
        public int compare(TacletAppListItem arg0, TacletAppListItem arg1) {
        
            return arg0.shortDescription().compareTo(arg1.shortDescription());
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
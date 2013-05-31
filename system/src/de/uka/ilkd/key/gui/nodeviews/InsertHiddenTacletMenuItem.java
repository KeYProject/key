// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 


package de.uka.ilkd.key.gui.nodeviews;

import javax.swing.JFrame;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.rule.NoFindTaclet;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.tacletbuilder.TacletGoalTemplate;

/**
 * This item groups all insert hidden taclets and offers a
 * more convienient user interface to add them.
 *
 */
public class InsertHiddenTacletMenuItem extends InsertionTacletBrowserMenuItem {
    
   
    /**
     * 
     */
    private static final long serialVersionUID = -2221016383998349319L;

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
        
        final ImmutableList<TacletGoalTemplate> goalTemplates = t.goalTemplates(); 
        if (goalTemplates.size() != 1) return null;
        return goalTemplates.head().sequent();
    }
}

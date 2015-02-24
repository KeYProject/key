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

/*
 * Created on Apr 18, 2005
 */
package de.uka.ilkd.key.gui.nodeviews;

import java.awt.event.ActionListener;

import javax.swing.JMenu;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.rule.PosTacletApp;

/**
 * This simple taclet menu displays the user a list of applicable taclets
 * and lets select her/him one of those. It is similar to 
 * {@link de.uka.ilkd.key.gui.nodeviews.TacletMenu} but with some important differences:
 * <ul>
 * <li> it returns the selected taclet app and does not initiate any further
 * action as the original {@link de.uka.ilkd.key.gui.nodeviews.TacletMenu} </li>
 * <li> it does not display any additional menu entries like: 
 *    Apply strategies here, built-in rules, abbreviation etc.
 * </li>
 * </ul> 
 */
public class SimpleTacletSelectionMenu extends JMenu {

    /**
     * 
     */
    private static final long serialVersionUID = 3027934580300468044L;

    /**
     * creates an instance of this menu displaying the applications stored in
     * <tt>apps</tt>
     * @param apps the IList<PosTacletApp> to be displayed
     * @param info the NotationInfo used to pretty print the taclets in 
     * tooltips
     * @param listener the ActionListener which is registered at each 
     * menu item 
     */
    public SimpleTacletSelectionMenu(ImmutableList<PosTacletApp> apps, 
            NotationInfo info, ActionListener listener, Services services) {
        super("Select Rule to Apply");        
                    
        addMenuEntries(apps, info, listener, services);
    }

    /**
     * adds the given applications to the menu
     * @param apps the IList<PosTacletApp> to be displayed
     * @param info the NotationInfo used to pretty print the taclets in 
     * tooltips
     * @param listener the ActionListener which is registered at each 
     * menu item 
     */
    private void addMenuEntries(ImmutableList<PosTacletApp> apps, 
            NotationInfo info, ActionListener listener, Services services) {
        for (PosTacletApp app : apps) {
            final DefaultTacletMenuItem item =
                    new DefaultTacletMenuItem(this, app, info, services);
            item.addActionListener(listener);
            add(item);
        }
    }
}
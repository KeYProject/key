// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.asmkey.gui;


import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

import javax.swing.JMenu;
import javax.swing.JMenuItem;

import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.rule.IteratorOfBuiltInRule;
import de.uka.ilkd.key.rule.ListOfBuiltInRule;


/** This class implements the lemma menu which
 * permits to add any lemma. 
 * Contrary to the lemmas in the taclet menu, which
 * appears only on a match between the current
 * goal and the different lemmas.
 *
 * @author Stanislas Nanchen
*/


public class LemmaMenu extends JMenu {

    private static String menuName = "Lemmas";

    private KeYMediator keyMediator;

    public LemmaMenu(KeYMediator keyMediator, ListOfBuiltInRule lemmaRules) {
	super(menuName);
	
	this.keyMediator = keyMediator;
	buildMenu(lemmaRules);
    }

    private void buildMenu(ListOfBuiltInRule lemmaRules) {
	IteratorOfBuiltInRule it = lemmaRules.iterator();
	boolean hasLemmas;
	JMenuItem menuItem;
	ActionListener menuControl =
	    new ActionListener() {
		public void actionPerformed(ActionEvent e) {
		    /*if (e.getSource() instanceof LemmaRuleMenuItem) {
			keyMediator.selectedBuiltInRule
			    (((LemmaRuleMenuItem) e.getSource()).connectedTo(),
			     PosInSequent.createSequentPos());
			     }*/
		}
	    };

	/* determines if we have lemmas */
	hasLemmas = it.hasNext();

	/* Iterates through the LemmaRule list and add 
	 * a JMenuItem to the menu for each lemmaRule 
	 */
	while(it.hasNext()) {
	    menuItem = null;//new LemmaRuleMenuItem((LemmaRule) it.next());
	    menuItem.addActionListener(menuControl);
	    add(menuItem);
	}

	addSeparator();

	/* Then add a menu item for lemma dialog
	 * if we have lemmas
	 */
	menuItem = new JMenuItem("View all Lemmas");
	menuItem.addActionListener(menuControl);
	menuItem.setEnabled(false);
	add(menuItem);

	/* Finaly, we have the menu item for
	 * creating new lemmas
	 */
	menuItem = new JMenuItem("Create new Lemma");
	menuItem.addActionListener(menuControl);
	menuItem.setEnabled(false);
	add(menuItem);
    }

}

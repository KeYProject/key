/*
 * Created on Apr 18, 2005
 */
package de.uka.ilkd.key.gui.nodeviews;

import java.awt.event.ActionListener;

import javax.swing.JMenu;

import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.rule.IteratorOfPosTacletApp;
import de.uka.ilkd.key.rule.ListOfPosTacletApp;

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
     * creates an instance of this menu displaying the applications stored in
     * <tt>apps</tt>
     * @param apps the ListOfPosTacletApp to be displayed
     * @param info the NotationInfo used to pretty print the taclets in 
     * tooltips
     * @param listener the ActionListener which is registered at each 
     * menu item 
     */
    public SimpleTacletSelectionMenu(ListOfPosTacletApp apps, 
            NotationInfo info, ActionListener listener) {
        super("Select Rule to Apply");        
                    
        addMenuEntries(apps, info, listener);           
    }

    /**
     * adds the given applications to the menu
     * @param apps the ListOfPosTacletApp to be displayed
     * @param info the NotationInfo used to pretty print the taclets in 
     * tooltips
     * @param listener the ActionListener which is registered at each 
     * menu item 
     */
    private void addMenuEntries(ListOfPosTacletApp apps, 
            NotationInfo info, ActionListener listener) {
        final IteratorOfPosTacletApp it = apps.iterator();
        while (it.hasNext()) {
            final DefaultTacletMenuItem item = 
                new DefaultTacletMenuItem(this, it.next(), info);
            item.addActionListener(listener);
            add(item);
        }
    }
}

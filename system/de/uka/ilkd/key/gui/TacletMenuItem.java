package de.uka.ilkd.key.gui;

import java.awt.event.ActionListener;

import de.uka.ilkd.key.rule.TacletApp;

/**
 * This interface is implemented by items to be displayed in 
 * the @link TacletMenu.
 */
interface TacletMenuItem {
    
    
    void addActionListener(ActionListener listener);
    
    /** gets the Taclet that is attached to this item
     * @return the attached Taclet
     */
    abstract TacletApp connectedTo();

}

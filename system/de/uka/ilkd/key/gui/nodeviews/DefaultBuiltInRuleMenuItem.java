package de.uka.ilkd.key.gui.nodeviews;

import javax.swing.JMenuItem;

import de.uka.ilkd.key.rule.BuiltInRule;

/** 
 * equal to TacletMenuItem but for BuiltInRules
 */
class DefaultBuiltInRuleMenuItem extends JMenuItem implements BuiltInRuleMenuItem {
    
    private BuiltInRule connectedTo;
    
    public DefaultBuiltInRuleMenuItem(BuiltInRule connectedTo) {
        super(connectedTo.name().toString());
        this.connectedTo = connectedTo;	    	    
    } 

    public BuiltInRule connectedTo() {
        return connectedTo;
    }

}

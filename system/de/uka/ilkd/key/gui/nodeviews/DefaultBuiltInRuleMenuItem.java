// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.gui.nodeviews;

import javax.swing.JMenuItem;

import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.smt.SMTRule;

/** 
 * equal to TacletMenuItem but for BuiltInRules
 */
class DefaultBuiltInRuleMenuItem extends JMenuItem implements BuiltInRuleMenuItem {
    
    private BuiltInRule connectedTo;
    
    public DefaultBuiltInRuleMenuItem(BuiltInRule connectedTo) {
        super(connectedTo.name().toString());
        this.connectedTo = connectedTo;
        //if the rule is not installed, don't make it useable.
        if (connectedTo instanceof SMTRule) {
            if (!((SMTRule)connectedTo).isInstalled(false)) {
        	this.setEnabled(false);
            }
        }
    } 

    public BuiltInRule connectedTo() {
        return connectedTo;
    }

}

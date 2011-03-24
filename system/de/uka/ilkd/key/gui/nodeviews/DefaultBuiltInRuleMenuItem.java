// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.gui.nodeviews;

import javax.swing.JMenuItem;

import de.uka.ilkd.key.rule.BuiltInRule;


/** 
 * equal to TacletMenuItem but for BuiltInRules
 */
class DefaultBuiltInRuleMenuItem extends JMenuItem implements BuiltInRuleMenuItem {
    
    private BuiltInRule connectedTo;
    
    public DefaultBuiltInRuleMenuItem(BuiltInRule connectedTo) {
        super(connectedTo.toString());
        this.connectedTo = connectedTo;


    } 

    public BuiltInRule connectedTo() {
        return connectedTo;
    }

}

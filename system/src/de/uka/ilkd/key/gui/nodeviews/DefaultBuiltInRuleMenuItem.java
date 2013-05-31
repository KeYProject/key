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

import javax.swing.JMenuItem;

import de.uka.ilkd.key.rule.BuiltInRule;


/** 
 * equal to TacletMenuItem but for BuiltInRules
 */
class DefaultBuiltInRuleMenuItem extends JMenuItem implements BuiltInRuleMenuItem {
    
    /**
     * 
     */
    private static final long serialVersionUID = 2104546363767367689L;
    private BuiltInRule connectedTo;
    private final boolean forced;
    

    public DefaultBuiltInRuleMenuItem(String title, BuiltInRule connectedTo, boolean forced) {
        super(title);
        this.connectedTo = connectedTo;
        this.forced = forced;
    } 

    public DefaultBuiltInRuleMenuItem(BuiltInRule connectedTo, boolean forced) {
        this(connectedTo.toString(),connectedTo, forced);
    } 

    public DefaultBuiltInRuleMenuItem(BuiltInRule connectedTo) {
        this(connectedTo, false);
    } 

    
    public BuiltInRule connectedTo() {
        return connectedTo;
    }

    @Override
    public boolean forcedApplication() {
        return forced;
    }

}

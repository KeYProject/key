// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof.mgt;

import java.util.LinkedHashMap;
import java.util.Map;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.rule.RuleApp;


public class ComplexRuleJustificationBySpec implements ComplexRuleJustification {

    private Map /*RuleApp -> RuleJustificationBySpec*/ app2Just 
        = new LinkedHashMap();
   
        
    public boolean isAxiomJustification() {
        return false;
    }
    
    
    public RuleJustification getSpecificJustification(RuleApp app, 
                                                      Services services) {
        RuleJustification result = (RuleJustification) app2Just.get(app);
        return result == null ? this : result;
    }
    
    
    public void add(RuleApp ruleApp, RuleJustificationBySpec just) {
	assert !(just instanceof ComplexRuleJustification);
        app2Just.put(ruleApp, just);
    }
}

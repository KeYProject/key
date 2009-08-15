// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//

package de.uka.ilkd.key.proof.mgt;

import java.util.HashMap;
import java.util.Map;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.rule.Rule;
import de.uka.ilkd.key.rule.RuleApp;


public class RuleJustificationInfo {

    private Map rule2justif = new HashMap();

    public void addJustification(Rule r, RuleJustification j) {
	rule2justif.put(r, j);
    }

    public RuleJustification getJustification(Rule r) {
	return (RuleJustification) rule2justif.get(r);
    }

    public RuleJustification getJustification(RuleApp r, Services services) {
	RuleJustification just = getJustification(r.rule());
        if (just instanceof ComplexRuleJustification) {
            return ((ComplexRuleJustification) just).getSpecificJustification(r, services);
        } else {
	    return just;
	}
    }    
}

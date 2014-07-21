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

package de.uka.ilkd.key.proof.mgt;

import java.util.LinkedHashMap;
import java.util.Map;

import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.rule.Rule;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.RuleKey;

public class RuleJustificationInfo {

    private Map<RuleKey, RuleJustification> rule2justif 
    	= new LinkedHashMap<RuleKey, RuleJustification>();

    public void addJustification(Rule r, RuleJustification j) {
        final RuleKey ruleKey = new RuleKey(r);
        if (rule2justif.containsKey(ruleKey)) {
            // TODO: avoid double registration of certain class axioms and remove then the below check so that 
            // always an exception will be thrown
            for (RuleKey key : rule2justif.keySet()) {
                if (key.equals(ruleKey) && r != key.r) {
                    throw new IllegalArgumentException("Rule " + r.name()
                            + " already in registered.");

               }
            }
         } else {
             rule2justif.put(ruleKey, j);
         }
    }

    public RuleJustification getJustification(Rule r) {
	return rule2justif.get(new RuleKey(r));
    }

    public RuleJustification getJustification(RuleApp r, TermServices services) {
	RuleJustification just = getJustification(r.rule());
        if (just instanceof ComplexRuleJustification) {
            return ((ComplexRuleJustification) just).getSpecificJustification(r, services);
        } else {
	    return just;
	}
    }

    public void removeJustificationFor(Rule rule) {
        rule2justif.remove(new RuleKey(rule));
     }

   public RuleJustificationInfo copy() {
      RuleJustificationInfo info = new RuleJustificationInfo();
      info.rule2justif.putAll(rule2justif);
      return info;
   }
}